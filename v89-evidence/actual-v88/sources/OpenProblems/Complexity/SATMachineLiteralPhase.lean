import OpenProblems.Complexity.SATMachineFormulaPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState
open SATMachineControl

@[simp] theorem step_literalSign_raw
    (formulaValue clauseValue positive : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (literalSign formulaValue clauseValue) blank left
        (ofBool positive :: right)) =
    configAt (indexRead formulaValue clauseValue positive) blank
      (processed :: left) right := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Canonical state after consuming a literal sign bit and before scanning its
unary variable index. -/
def literalIndexEntryConfig
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt (indexRead formulaValue clauseValue positive) blank
    (processed :: clauseEnd :: clauseSpent ::
      List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (List.replicate index (ofBool true) ++ ofBool false ::
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- The literal sign is consumed in one exact transition. -/
theorem run_literalSign_to_indexRead
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run 1
      (firstLiteralSignConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals
        (positive :: List.replicate index true ++ [false])
        restLiteralPayload restPayload assignment suffix) =
    literalIndexEntryConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals index restLiteralPayload restPayload
      assignment suffix := by
  rw [controlMachine_run_one]
  unfold firstLiteralSignConfig literalIndexEntryConfig
  simp only [List.map_append, List.map_cons, List.map_replicate, List.cons_append]
  rw [step_literalSign_raw]
  simp [List.append_assoc]

@[simp] theorem step_indexRead_true
    (formulaValue clauseValue positive : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (indexRead formulaValue clauseValue positive) blank left
        (ofBool true :: right)) =
    configAt (indexRead formulaValue clauseValue positive) blank
      (indexLive :: left) right := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Exact unary scan of a literal variable index. -/
theorem run_indexRead_trues
    (formulaValue clauseValue positive : Bool)
    (n : Nat) (left payload : List SATMachineSymbol) :
    satControl.run n
      (configAt (indexRead formulaValue clauseValue positive) blank left
        (List.replicate n (ofBool true) ++ payload)) =
    configAt (indexRead formulaValue clauseValue positive) blank
      (List.replicate n indexLive ++ left) payload := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 = 1 + n by omega]
      rw [controlMachine_run_add, controlMachine_run_one]
      simp only [List.cons_append]
      rw [step_indexRead_true]
      simpa [List.replicate_succ, List.append_assoc, Nat.add_comm,
        replicate_append_same_marker] using
        (ih (left := indexLive :: left))

@[simp] theorem step_indexRead_false
    (formulaValue clauseValue positive : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (indexRead formulaValue clauseValue positive) blank
        (leftHead :: leftTail) (ofBool false :: right)) =
    configAt (lookupSelect formulaValue clauseValue positive) blank leftTail
      (leftHead :: indexEnd :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Canonical lookup-selection cursor after the literal index terminator.  For
index zero the cursor is already at the processed sign marker; for a positive
index it is at the rightmost live unary index marker. -/
def literalLookupSelectConfig
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  let baseLeft :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let right :=
    indexEnd :: restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool
  match index with
  | 0 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank baseLeft
        (processed :: right)
  | k + 1 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank
        (List.replicate k indexLive ++ processed :: baseLeft)
        (indexLive :: right)

/-- Unary literal-index decoding reaches the lookup selector in exactly
`index + 1` steps after the sign has been consumed. -/
theorem run_indexRead_to_lookupSelect
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run (index + 1)
      (literalIndexEntryConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals index restLiteralPayload restPayload
        assignment suffix) =
    literalLookupSelectConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals index restLiteralPayload restPayload
      assignment suffix := by
  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let payload : List SATMachineSymbol :=
    ofBool false :: restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
      List.replicate variableCount assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool
  have hscan := run_indexRead_trues formulaValue clauseValue positive index
    (processed :: baseLeft) payload
  have hscan' :
      satControl.run index
        (literalIndexEntryConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals index restLiteralPayload restPayload
          assignment suffix) =
      configAt (indexRead formulaValue clauseValue positive) blank
        (List.replicate index indexLive ++ processed :: baseLeft) payload := by
    unfold literalIndexEntryConfig baseLeft payload at hscan ⊢
    simpa [List.append_assoc] using hscan
  rw [show index + 1 = index + 1 by rfl]
  rw [controlMachine_run_add, hscan', controlMachine_run_one]
  cases index with
  | zero =>
      simp only [List.replicate_zero, List.nil_append]
      dsimp [payload]
      rw [step_indexRead_false]
      unfold literalLookupSelectConfig baseLeft
      simp [List.append_assoc]
  | succ k =>
      rw [List.replicate_succ]
      simp only [List.cons_append]
      dsimp [payload]
      rw [step_indexRead_false]
      unfold literalLookupSelectConfig baseLeft
      simp [List.append_assoc]

/-- A canonically encoded literal reaches the lookup selector after exactly
`index + 2` machine steps from its sign bit. -/
theorem run_literal_to_lookupSelect
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    satControl.run (index + 2)
      (firstLiteralSignConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals
        (positive :: List.replicate index true ++ [false])
        restLiteralPayload restPayload assignment suffix) =
    literalLookupSelectConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals index restLiteralPayload restPayload
      assignment suffix := by
  rw [show index + 2 = 1 + (index + 1) by omega]
  rw [controlMachine_run_add]
  rw [run_literalSign_to_indexRead]
  exact run_indexRead_to_lookupSelect formulaValue clauseValue positive
    variableCount remainingClauses remainingLiterals index restLiteralPayload
    restPayload assignment suffix


/-- Symbols crossed to the right between an index-zero literal and the payload
separator. -/
def zeroLookupRightMarkers
    (restLiteralPayload restPayload : BitString) : List SATMachineSymbol :=
  indexEnd :: restLiteralPayload.map ofBool ++ restPayload.map ofBool

def zeroLookupRightMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = indexEnd ∨ ∃ bit : Bool, symbol = ofBool bit

@[simp] theorem step_lookupTargetRight_zeroMarker
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol)
    (h : zeroLookupRightMarker symbol)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupTargetRight formulaValue clauseValue positive) blank left
        (symbol :: right)) =
    configAt (lookupTargetRight formulaValue clauseValue positive) blank
      (symbol :: left) right := by
  rcases h with rfl | ⟨bit, rfl⟩
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> cases bit <;> rfl

theorem zeroLookupRightMarkers_all
    (restLiteralPayload restPayload : BitString)
    (symbol : SATMachineSymbol)
    (hmem : symbol ∈ zeroLookupRightMarkers restLiteralPayload restPayload) :
    zeroLookupRightMarker symbol := by
  unfold zeroLookupRightMarkers at hmem
  simp only [List.mem_cons, List.mem_append] at hmem
  rcases hmem with hmain | hright
  · rcases hmain with hzero | hleft
    · exact Or.inl hzero
    · rcases List.mem_map.mp hleft with ⟨bit, _, rfl⟩
      exact Or.inr ⟨bit, rfl⟩
  · rcases List.mem_map.mp hright with ⟨bit, _, rfl⟩
    exact Or.inr ⟨bit, rfl⟩

@[simp] theorem zeroLookupRightMarkers_length
    (restLiteralPayload restPayload : BitString) :
    (zeroLookupRightMarkers restLiteralPayload restPayload).length =
      1 + restLiteralPayload.length + restPayload.length := by
  simp [zeroLookupRightMarkers]
  omega

@[simp] theorem step_lookupTargetRight_separator
    (formulaValue clauseValue positive : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupTargetRight formulaValue clauseValue positive) blank left
        (separator :: right)) =
    configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
      (separator :: left) right := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Checked certificate-length markers and their end marker are skipped before
consulting the normalized assignment. -/
def zeroLookupCertificateMarkers (variableCount : Nat) : List SATMachineSymbol :=
  List.replicate variableCount assignmentLengthChecked ++ [assignmentLengthEnd]

def zeroLookupCertificateMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = assignmentLengthChecked ∨ symbol = assignmentLengthEnd

@[simp] theorem step_lookupTargetCertificate_marker
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol)
    (h : zeroLookupCertificateMarker symbol)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank left
        (symbol :: right)) =
    configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
      (symbol :: left) right := by
  rcases h with rfl | rfl <;>
    cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

theorem zeroLookupCertificateMarkers_all
    (variableCount : Nat) (symbol : SATMachineSymbol)
    (hmem : symbol ∈ zeroLookupCertificateMarkers variableCount) :
    zeroLookupCertificateMarker symbol := by
  unfold zeroLookupCertificateMarkers at hmem
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hmem
  rcases hmem with h | h
  · exact Or.inl h.2
  · exact Or.inr h

@[simp] theorem zeroLookupCertificateMarkers_length (variableCount : Nat) :
    (zeroLookupCertificateMarkers variableCount).length = variableCount + 1 := by
  simp [zeroLookupCertificateMarkers]

@[simp] theorem step_lookupTargetCertificate_assignment
    (formulaValue clauseValue positive value : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank left
        (assignmentSymbol value :: right)) =
    match left with
    | [] =>
        configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
          blank [] (blank :: assignmentSymbol value :: right)
    | head :: tail =>
        configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
          blank tail (head :: assignmentSymbol value :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> cases value <;>
    cases left <;> rfl

/-- Markers crossed while returning left from assignment zero to the literal's
index terminator. -/
def zeroLookupReturnMarkers
    (variableCount : Nat)
    (restLiteralPayload restPayload : BitString) : List SATMachineSymbol :=
  assignmentLengthEnd :: List.replicate variableCount assignmentLengthChecked ++
    separator :: (restPayload.map ofBool).reverse ++
      (restLiteralPayload.map ofBool).reverse

def zeroLookupReturnMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = assignmentLengthEnd ∨
  symbol = assignmentLengthChecked ∨
  symbol = separator ∨
  ∃ bit : Bool, symbol = ofBool bit

@[simp] theorem step_cleanupReturn_zeroMarker
    (formulaValue clauseValue literalValue : Bool)
    (symbol : SATMachineSymbol)
    (h : zeroLookupReturnMarker symbol)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (cleanupReturn formulaValue clauseValue literalValue) blank
        (leftHead :: leftTail) (symbol :: right)) =
    configAt (cleanupReturn formulaValue clauseValue literalValue) blank leftTail
      (leftHead :: symbol :: right) := by
  rcases h with hend | hchecked | hsep | hraw
  · subst symbol
    cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl
  · subst symbol
    cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl
  · subst symbol
    cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl
  · rcases hraw with ⟨bit, rfl⟩
    cases bit <;> cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl

theorem zeroLookupReturnMarkers_all
    (variableCount : Nat)
    (restLiteralPayload restPayload : BitString)
    (symbol : SATMachineSymbol)
    (hmem : symbol ∈ zeroLookupReturnMarkers variableCount restLiteralPayload restPayload) :
    zeroLookupReturnMarker symbol := by
  unfold zeroLookupReturnMarkers at hmem
  simp only [List.mem_cons, List.mem_append, List.mem_replicate] at hmem
  rcases hmem with hmain | hlit
  · rcases hmain with hprefix | hrest
    · rcases hprefix with hend | hchecked
      · exact Or.inl hend
      · exact Or.inr (Or.inl hchecked.2)
    · rcases hrest with hsep | hraw
      · exact Or.inr (Or.inr (Or.inl hsep))
      · have hm : symbol ∈ restPayload.map ofBool := List.mem_reverse.mp hraw
        rcases List.mem_map.mp hm with ⟨bit, _, rfl⟩
        exact Or.inr (Or.inr (Or.inr ⟨bit, rfl⟩))
  · have hm : symbol ∈ restLiteralPayload.map ofBool := List.mem_reverse.mp hlit
    rcases List.mem_map.mp hm with ⟨bit, _, rfl⟩
    exact Or.inr (Or.inr (Or.inr ⟨bit, rfl⟩))

@[simp] theorem zeroLookupReturnMarkers_length
    (variableCount : Nat)
    (restLiteralPayload restPayload : BitString) :
    (zeroLookupReturnMarkers variableCount restLiteralPayload restPayload).length =
      variableCount + restLiteralPayload.length + restPayload.length + 2 := by
  simp [zeroLookupReturnMarkers]
  omega

@[simp] theorem zeroLookupReturnMarkers_reverse
    (variableCount : Nat)
    (restLiteralPayload restPayload : BitString) :
    (zeroLookupReturnMarkers variableCount restLiteralPayload restPayload).reverse =
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++ [assignmentLengthEnd] := by
  simp [zeroLookupReturnMarkers, List.reverse_append, List.append_assoc]

@[simp] theorem step_cleanupReturn_indexEnd
    (formulaValue clauseValue literalValue : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (cleanupReturn formulaValue clauseValue literalValue) blank
        (leftHead :: leftTail) (indexEnd :: right)) =
    configAt (cleanupIndex formulaValue clauseValue literalValue) blank leftTail
      (leftHead :: processed :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl

@[simp] theorem step_cleanupIndex_processed
    (formulaValue clauseValue literalValue : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (cleanupIndex formulaValue clauseValue literalValue) blank
        (leftHead :: leftTail) (processed :: right)) =
    configAt (clauseFind formulaValue (clauseValue || literalValue)) blank leftTail
      (leftHead :: processed :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl

/-- Canonical state after a zero-index literal has been evaluated and the
literal/index scratch region has been cleaned. -/
def zeroLiteralEvaluatedConfig
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (restLiteralPayload restPayload assignmentRest suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt
    (clauseFind formulaValue (clauseValue || applyPolarity positive value)) blank
    (clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseEnd :: processed :: processed ::
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: assignmentSymbol value ::
            assignmentRest.map assignmentSymbol ++ suffix.map ofBool)

/-- Exact zero-index lookup: assignment slot zero is read, polarity is applied,
and the machine returns to `clauseFind` with the clause accumulator updated. -/
theorem run_lookup_zero
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (restLiteralPayload restPayload assignmentRest suffix : BitString) :
    satControl.run
      (2 * (variableCount + restLiteralPayload.length + restPayload.length) + 9)
      (literalLookupSelectConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals 0 restLiteralPayload restPayload
        (value :: assignmentRest) suffix) =
    zeroLiteralEvaluatedConfig formulaValue clauseValue positive value variableCount
      remainingClauses remainingLiterals restLiteralPayload restPayload
      assignmentRest suffix := by
  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let rightMarkers := zeroLookupRightMarkers restLiteralPayload restPayload
  let certMarkers := zeroLookupCertificateMarkers variableCount
  let returnMarkers :=
    zeroLookupReturnMarkers variableCount restLiteralPayload restPayload
  let assignmentRight : List SATMachineSymbol :=
    assignmentSymbol value :: assignmentRest.map assignmentSymbol ++ suffix.map ofBool
  have hselect :
      satControl.run 1
        (literalLookupSelectConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals 0 restLiteralPayload restPayload
          (value :: assignmentRest) suffix) =
      configAt (lookupTargetRight formulaValue clauseValue positive) blank
        (processed :: baseLeft)
        (rightMarkers ++ (separator :: certMarkers ++ assignmentRight)) := by
    rw [controlMachine_run_one]
    unfold literalLookupSelectConfig baseLeft rightMarkers certMarkers assignmentRight
    unfold zeroLookupRightMarkers zeroLookupCertificateMarkers
    cases formulaValue <;> cases clauseValue <;> cases positive <;> cases value <;>
      simp [List.append_assoc]
    all_goals rfl
  have hright := run_keepRight_markers
    (lookupTargetRight formulaValue clauseValue positive)
    zeroLookupRightMarker rightMarkers (processed :: baseLeft)
    (separator :: certMarkers ++ assignmentRight)
    (step_lookupTargetRight_zeroMarker formulaValue clauseValue positive)
    (zeroLookupRightMarkers_all restLiteralPayload restPayload)
  have hsep :
      satControl.run 1
        (configAt (lookupTargetRight formulaValue clauseValue positive) blank
          (rightMarkers.reverse ++ processed :: baseLeft)
          (separator :: certMarkers ++ assignmentRight)) =
      configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
        (separator :: rightMarkers.reverse ++ processed :: baseLeft)
        (certMarkers ++ assignmentRight) := by
    rw [controlMachine_run_one]
    exact step_lookupTargetRight_separator _ _ _ _ _
  have hcert := run_keepRight_markers
    (lookupTargetCertificate formulaValue clauseValue positive)
    zeroLookupCertificateMarker certMarkers
    (separator :: rightMarkers.reverse ++ processed :: baseLeft)
    assignmentRight
    (step_lookupTargetCertificate_marker formulaValue clauseValue positive)
    (zeroLookupCertificateMarkers_all variableCount)
  have hvalue :
      satControl.run 1
        (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
          (certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ processed :: baseLeft))
          assignmentRight) =
      keepLeftScanConfig
        (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
        returnMarkers indexEnd (processed :: baseLeft)
        assignmentRight := by
    rw [controlMachine_run_one]
    unfold assignmentRight certMarkers rightMarkers returnMarkers
    unfold zeroLookupCertificateMarkers zeroLookupRightMarkers zeroLookupReturnMarkers
    simp [keepLeftScanConfig, List.reverse_append, List.append_assoc]
  have hreturn := run_keepLeft_markers
    (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
    zeroLookupReturnMarker returnMarkers indexEnd (processed :: baseLeft)
    assignmentRight
    (step_cleanupReturn_zeroMarker formulaValue clauseValue (applyPolarity positive value))
    (zeroLookupReturnMarkers_all variableCount restLiteralPayload restPayload)
  have hend :
      satControl.run 1
        (configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
          blank (processed :: baseLeft)
          (indexEnd :: returnMarkers.reverse ++ assignmentRight)) =
      configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
        blank baseLeft
        (processed :: processed :: returnMarkers.reverse ++ assignmentRight) := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_cleanupReturn_indexEnd]
  have hclean :
      satControl.run 1
        (configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
          blank baseLeft
          (processed :: processed :: returnMarkers.reverse ++ assignmentRight)) =
      zeroLiteralEvaluatedConfig formulaValue clauseValue positive value variableCount
        remainingClauses remainingLiterals restLiteralPayload restPayload
        assignmentRest suffix := by
    rw [controlMachine_run_one]
    unfold baseLeft
    cases remainingLiterals with
    | zero =>
        simp only [List.replicate_zero, List.nil_append, List.cons_append]
        rw [step_cleanupIndex_processed]
        unfold zeroLiteralEvaluatedConfig returnMarkers assignmentRight
        simp [zeroLookupReturnMarkers_reverse, List.append_assoc]
    | succ k =>
        rw [List.replicate_succ]
        simp only [List.cons_append]
        rw [step_cleanupIndex_processed]
        unfold zeroLiteralEvaluatedConfig returnMarkers assignmentRight
        rw [List.replicate_succ]
        simp [zeroLookupReturnMarkers_reverse, List.append_assoc]
  have hlenRight : rightMarkers.length =
      1 + restLiteralPayload.length + restPayload.length := by
    exact zeroLookupRightMarkers_length _ _
  have hlenCert : certMarkers.length = variableCount + 1 := by
    exact zeroLookupCertificateMarkers_length _
  have hlenReturn : returnMarkers.length =
      variableCount + restLiteralPayload.length + restPayload.length + 2 := by
    exact zeroLookupReturnMarkers_length _ _ _
  rw [show 2 * (variableCount + restLiteralPayload.length + restPayload.length) + 9 =
      1 + (rightMarkers.length + (1 + (certMarkers.length +
        (1 + (returnMarkers.length + (1 + 1)))))) by omega]
  rw [controlMachine_run_add, hselect]
  rw [controlMachine_run_add, hright]
  rw [controlMachine_run_add, hsep]
  rw [controlMachine_run_add, hcert]
  rw [controlMachine_run_add, hvalue]
  rw [controlMachine_run_add, hreturn]
  rw [controlMachine_run_add, hend]
  exact hclean

end SATMachineCertificatePhase
end OpenProblems.Complexity
