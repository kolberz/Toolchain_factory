import OpenProblems.Complexity.SATMachineLiteralPhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState SATMachineControl

/-- Value-preserving visited marker used while skipping earlier assignment
slots during an indexed literal lookup. -/
def assignmentVisitedSymbol (bit : Bool) : SATMachineSymbol :=
  if bit then assignmentVisitedTrue else assignmentVisitedFalse

@[simp] theorem assignmentVisitedSymbol_false :
    assignmentVisitedSymbol false = assignmentVisitedFalse := rfl

@[simp] theorem assignmentVisitedSymbol_true :
    assignmentVisitedSymbol true = assignmentVisitedTrue := rfl

/-- General lookup-loop configuration. `visited` records assignment slots
already skipped by unary index markers. `indexRemaining` is the number of live
index markers still to consume. -/
def lookupLoopConfig
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString) (indexRemaining : Nat)
    (restLiteralPayload restPayload remainingAssignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  let baseLeft :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let afterIndex :=
    List.replicate visited.length indexSpent ++ indexEnd ::
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: visited.map assignmentVisitedSymbol ++
            remainingAssignment.map assignmentSymbol ++ suffix.map ofBool
  match indexRemaining with
  | 0 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank baseLeft
        (processed :: afterIndex)
  | k + 1 =>
      configAt (lookupSelect formulaValue clauseValue positive) blank
        (List.replicate k indexLive ++ processed :: baseLeft)
        (indexLive :: afterIndex)

/-- The literal parser's initial lookup selector is the general lookup loop
with no assignment slots visited yet. -/
theorem literalLookupSelectConfig_eq_lookupLoopConfig
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals index : Nat)
    (restLiteralPayload restPayload assignment suffix : BitString) :
    literalLookupSelectConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals index restLiteralPayload restPayload
      assignment suffix =
    lookupLoopConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals [] index restLiteralPayload restPayload
      assignment suffix := by
  cases index <;>
    simp [literalLookupSelectConfig, lookupLoopConfig, List.append_assoc]

@[simp] theorem step_lookupSelect_live
    (formulaValue clauseValue positive : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupSelect formulaValue clauseValue positive) blank left
        (indexLive :: right)) =
    configAt (lookupSkipRight formulaValue clauseValue positive) blank
      (indexSpent :: left) right := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Markers crossed to the right after consuming one live unary index marker. -/
def lookupSkipRightMarkers
    (visitedCount : Nat)
    (restLiteralPayload restPayload : BitString) : List SATMachineSymbol :=
  List.replicate visitedCount indexSpent ++
    zeroLookupRightMarkers restLiteralPayload restPayload

def lookupSkipRightMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = indexSpent ∨ zeroLookupRightMarker symbol

@[simp] theorem step_lookupSkipRight_marker
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol)
    (h : lookupSkipRightMarker symbol)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupSkipRight formulaValue clauseValue positive) blank left
        (symbol :: right)) =
    configAt (lookupSkipRight formulaValue clauseValue positive) blank
      (symbol :: left) right := by
  rcases h with rfl | hzero
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · rcases hzero with rfl | ⟨bit, rfl⟩
    · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
    · cases bit <;> cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

theorem lookupSkipRightMarkers_all
    (visitedCount : Nat)
    (restLiteralPayload restPayload : BitString)
    (symbol : SATMachineSymbol)
    (hmem : symbol ∈ lookupSkipRightMarkers visitedCount restLiteralPayload restPayload) :
    lookupSkipRightMarker symbol := by
  unfold lookupSkipRightMarkers at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hspent | hzero
  · exact Or.inl (List.eq_of_mem_replicate hspent)
  · exact Or.inr
      (zeroLookupRightMarkers_all restLiteralPayload restPayload symbol hzero)

@[simp] theorem lookupSkipRightMarkers_length
    (visitedCount : Nat)
    (restLiteralPayload restPayload : BitString) :
    (lookupSkipRightMarkers visitedCount restLiteralPayload restPayload).length =
      visitedCount + 1 + restLiteralPayload.length + restPayload.length := by
  simp [lookupSkipRightMarkers, zeroLookupRightMarkers]
  omega

@[simp] theorem step_lookupSkipRight_separator
    (formulaValue clauseValue positive : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupSkipRight formulaValue clauseValue positive) blank left
        (separator :: right)) =
    configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
      (separator :: left) right := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Certificate prefix crossed before selecting the next unvisited assignment
slot: checked length markers, the length end marker, then previously visited
assignment values. -/
def lookupSkipCertificateMarkers
    (variableCount : Nat) (visited : BitString) : List SATMachineSymbol :=
  zeroLookupCertificateMarkers variableCount ++ visited.map assignmentVisitedSymbol

def lookupSkipCertificateMarker (symbol : SATMachineSymbol) : Prop :=
  zeroLookupCertificateMarker symbol ∨
    symbol = assignmentVisitedFalse ∨ symbol = assignmentVisitedTrue

@[simp] theorem step_lookupSkipCertificate_marker
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol)
    (h : lookupSkipCertificateMarker symbol)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupSkipCertificate formulaValue clauseValue positive) blank left
        (symbol :: right)) =
    configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
      (symbol :: left) right := by
  rcases h with hcert | rfl | rfl
  · rcases hcert with rfl | rfl <;>
      cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

theorem lookupSkipCertificateMarkers_all
    (variableCount : Nat) (visited : BitString)
    (symbol : SATMachineSymbol)
    (hmem : symbol ∈ lookupSkipCertificateMarkers variableCount visited) :
    lookupSkipCertificateMarker symbol := by
  unfold lookupSkipCertificateMarkers at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hcert | hvisited
  · exact Or.inl
      (zeroLookupCertificateMarkers_all variableCount symbol hcert)
  · rcases List.mem_map.mp hvisited with ⟨bit, _, rfl⟩
    cases bit
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

@[simp] theorem lookupSkipCertificateMarkers_length
    (variableCount : Nat) (visited : BitString) :
    (lookupSkipCertificateMarkers variableCount visited).length =
      variableCount + 1 + visited.length := by
  simp [lookupSkipCertificateMarkers, zeroLookupCertificateMarkers]
  omega

@[simp] theorem step_lookupSkipCertificate_assignment
    (formulaValue clauseValue positive value : Bool)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupSkipCertificate formulaValue clauseValue positive) blank left
        (assignmentSymbol value :: right)) =
    match left with
    | [] =>
        configAt (lookupReturnIndex formulaValue clauseValue positive) blank []
          (blank :: assignmentVisitedSymbol value :: right)
    | head :: tail =>
        configAt (lookupReturnIndex formulaValue clauseValue positive) blank tail
          (head :: assignmentVisitedSymbol value :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> cases value <;>
    cases left <;> rfl

/-- Markers crossed to the left after marking one assignment slot visited and
before reaching the literal's index terminator. -/
def lookupReturnIndexMarkers
    (variableCount : Nat) (visited : BitString)
    (restLiteralPayload restPayload : BitString) : List SATMachineSymbol :=
  (visited.map assignmentVisitedSymbol).reverse ++
    (zeroLookupCertificateMarkers variableCount).reverse ++
      separator :: (restPayload.map ofBool).reverse ++
        (restLiteralPayload.map ofBool).reverse

def lookupReturnIndexMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = assignmentVisitedFalse ∨ symbol = assignmentVisitedTrue ∨
  zeroLookupCertificateMarker symbol ∨ symbol = separator ∨
  ∃ bit : Bool, symbol = ofBool bit

@[simp] theorem step_lookupReturnIndex_marker
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol)
    (h : lookupReturnIndexMarker symbol)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupReturnIndex formulaValue clauseValue positive) blank
        (leftHead :: leftTail) (symbol :: right)) =
    configAt (lookupReturnIndex formulaValue clauseValue positive) blank leftTail
      (leftHead :: symbol :: right) := by
  rcases h with rfl | rfl | hcert | rfl | ⟨bit, rfl⟩
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · rcases hcert with rfl | rfl <;>
      cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases bit <;> cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

theorem lookupReturnIndexMarkers_all
    (variableCount : Nat) (visited : BitString)
    (restLiteralPayload restPayload : BitString)
    (symbol : SATMachineSymbol)
    (hmem : symbol ∈ lookupReturnIndexMarkers variableCount visited
      restLiteralPayload restPayload) :
    lookupReturnIndexMarker symbol := by
  unfold lookupReturnIndexMarkers at hmem
  simp only [List.mem_cons, List.mem_append] at hmem
  rcases hmem with hmain | hlit
  · rcases hmain with hprefix | hrest
    · rcases hprefix with hvisited | hcert
      · have hm : symbol ∈ visited.map assignmentVisitedSymbol :=
          List.mem_reverse.mp hvisited
        rcases List.mem_map.mp hm with ⟨bit, _, rfl⟩
        cases bit
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have hm : symbol ∈ zeroLookupCertificateMarkers variableCount :=
          List.mem_reverse.mp hcert
        exact Or.inr (Or.inr (Or.inl
          (zeroLookupCertificateMarkers_all variableCount symbol hm)))
    · rcases hrest with hsep | hraw
      · exact Or.inr (Or.inr (Or.inr (Or.inl hsep)))
      · have hm : symbol ∈ restPayload.map ofBool := List.mem_reverse.mp hraw
        rcases List.mem_map.mp hm with ⟨bit, _, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨bit, rfl⟩)))
  · have hm : symbol ∈ restLiteralPayload.map ofBool := List.mem_reverse.mp hlit
    rcases List.mem_map.mp hm with ⟨bit, _, rfl⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨bit, rfl⟩)))

@[simp] theorem lookupReturnIndexMarkers_length
    (variableCount : Nat) (visited : BitString)
    (restLiteralPayload restPayload : BitString) :
    (lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload).length =
      visited.length + variableCount + restLiteralPayload.length + restPayload.length + 2 := by
  simp [lookupReturnIndexMarkers, zeroLookupCertificateMarkers]
  omega

@[simp] theorem lookupReturnIndexMarkers_reverse
    (variableCount : Nat) (visited : BitString)
    (restLiteralPayload restPayload : BitString) :
    (lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload).reverse =
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        zeroLookupCertificateMarkers variableCount ++ visited.map assignmentVisitedSymbol := by
  simp [lookupReturnIndexMarkers, List.reverse_append, List.append_assoc]

@[simp] theorem step_lookupReturnIndex_indexEnd
    (formulaValue clauseValue positive : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupReturnIndex formulaValue clauseValue positive) blank
        (leftHead :: leftTail) (indexEnd :: right)) =
    configAt (lookupSelect formulaValue clauseValue positive) blank leftTail
      (leftHead :: indexEnd :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

@[simp] theorem step_lookupSelect_spent
    (formulaValue clauseValue positive : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupSelect formulaValue clauseValue positive) blank
        (leftHead :: leftTail) (indexSpent :: right)) =
    configAt (lookupSelect formulaValue clauseValue positive) blank leftTail
      (leftHead :: indexSpent :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

@[simp] theorem replicate_append_same_singleton
    (n : Nat) (symbol : SATMachineSymbol) :
    List.replicate n symbol ++ [symbol] = List.replicate (n + 1) symbol := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

@[simp] theorem replicate_cons_same
    (n : Nat) (symbol : SATMachineSymbol) (tail : List SATMachineSymbol) :
    List.replicate n symbol ++ symbol :: tail =
      List.replicate (n + 1) symbol ++ tail := by
  change List.replicate n symbol ++ ([symbol] ++ tail) = _
  rw [← List.append_assoc]
  rw [replicate_append_same_singleton]

/-- Package the first left move after selecting an assignment value as the
canonical left-scan configuration. -/
theorem step_lookupSkipCertificate_assignment_keepLeft
    (formulaValue clauseValue positive value : Bool)
    (markers : List SATMachineSymbol) (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (hne : markers ≠ []) :
    satControl.run 1
      (configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
        (markers ++ baseHead :: baseLeft) (assignmentSymbol value :: right)) =
    keepLeftScanConfig (lookupReturnIndex formulaValue clauseValue positive)
      markers baseHead baseLeft (assignmentVisitedSymbol value :: right) := by
  rw [controlMachine_run_one]
  cases markers with
  | nil => exact (hne rfl).elim
  | cons marker remaining =>
      simp only [List.cons_append]
      rw [step_lookupSkipCertificate_assignment]
      rfl

/-- Package the first left move at the index terminator as the canonical scan
across the spent unary-index markers. -/
theorem step_lookupReturnIndex_indexEnd_keepLeft
    (formulaValue clauseValue positive : Bool)
    (markers : List SATMachineSymbol) (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (hne : markers ≠ []) :
    satControl.run 1
      (configAt (lookupReturnIndex formulaValue clauseValue positive) blank
        (markers ++ baseHead :: baseLeft) (indexEnd :: right)) =
    keepLeftScanConfig (lookupSelect formulaValue clauseValue positive)
      markers baseHead baseLeft (indexEnd :: right) := by
  rw [controlMachine_run_one]
  cases markers with
  | nil => exact (hne rfl).elim
  | cons marker remaining =>
      simp only [List.cons_append]
      rw [step_lookupReturnIndex_indexEnd]
      rfl

/-- One complete indexed skip iteration: consume one live unary index marker,
mark the next assignment value visited, return to the index block, and position
the lookup selector at the next live marker (or the processed sign marker). -/
theorem run_lookupLoop_one
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals indexTail : Nat)
    (visited : BitString)
    (restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (4 * visited.length +
        2 * variableCount +
        2 * (restLiteralPayload.length + restPayload.length) + 9)
      (lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited (indexTail + 1)
        restLiteralPayload restPayload (value :: assignmentTail) suffix) =
    lookupLoopConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals (visited ++ [value]) indexTail
      restLiteralPayload restPayload assignmentTail suffix := by
  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let rightMarkers :=
    lookupSkipRightMarkers visited.length restLiteralPayload restPayload
  let certMarkers := lookupSkipCertificateMarkers variableCount visited
  let returnMarkers :=
    lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload
  let assignmentRight : List SATMachineSymbol :=
    assignmentSymbol value :: assignmentTail.map assignmentSymbol ++ suffix.map ofBool
  have hselect :
      satControl.run 1
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited (indexTail + 1)
          restLiteralPayload restPayload (value :: assignmentTail) suffix) =
      configAt (lookupSkipRight formulaValue clauseValue positive) blank
        (indexSpent :: List.replicate indexTail indexLive ++ processed :: baseLeft)
        (rightMarkers ++ (separator :: certMarkers ++ assignmentRight)) := by
    rw [controlMachine_run_one]
    unfold lookupLoopConfig baseLeft rightMarkers certMarkers assignmentRight
    unfold lookupSkipRightMarkers lookupSkipCertificateMarkers
    unfold zeroLookupRightMarkers zeroLookupCertificateMarkers
    simp [List.append_assoc]
  have hright := run_keepRight_markers
    (lookupSkipRight formulaValue clauseValue positive)
    lookupSkipRightMarker rightMarkers
    (indexSpent :: List.replicate indexTail indexLive ++ processed :: baseLeft)
    (separator :: certMarkers ++ assignmentRight)
    (step_lookupSkipRight_marker formulaValue clauseValue positive)
    (lookupSkipRightMarkers_all visited.length restLiteralPayload restPayload)
  have hsep :
      satControl.run 1
        (configAt (lookupSkipRight formulaValue clauseValue positive) blank
          (rightMarkers.reverse ++ (indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft))
          (separator :: certMarkers ++ assignmentRight)) =
      configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
        (separator :: rightMarkers.reverse ++ (indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft))
        (certMarkers ++ assignmentRight) := by
    rw [controlMachine_run_one]
    exact step_lookupSkipRight_separator _ _ _ _ _
  have hcert := run_keepRight_markers
    (lookupSkipCertificate formulaValue clauseValue positive)
    lookupSkipCertificateMarker certMarkers
    (separator :: rightMarkers.reverse ++ (indexSpent ::
      List.replicate indexTail indexLive ++ processed :: baseLeft))
    assignmentRight
    (step_lookupSkipCertificate_marker formulaValue clauseValue positive)
    (lookupSkipCertificateMarkers_all variableCount visited)
  have hreturnMarkers_ne : returnMarkers ≠ [] := by
    unfold returnMarkers lookupReturnIndexMarkers zeroLookupCertificateMarkers
    simp
  have hleftLayout :
      certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ (indexSpent ::
        List.replicate indexTail indexLive ++ processed :: baseLeft)) =
      returnMarkers ++ indexEnd ::
        (List.replicate visited.length indexSpent ++ indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft) := by
    unfold certMarkers rightMarkers returnMarkers
    unfold lookupSkipCertificateMarkers lookupSkipRightMarkers
    unfold lookupReturnIndexMarkers zeroLookupCertificateMarkers zeroLookupRightMarkers
    simp [List.reverse_append, List.append_assoc]
  have hvalue :
      satControl.run 1
        (configAt (lookupSkipCertificate formulaValue clauseValue positive) blank
          (certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ (indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft)))
          assignmentRight) =
      keepLeftScanConfig (lookupReturnIndex formulaValue clauseValue positive)
        returnMarkers indexEnd
        (List.replicate visited.length indexSpent ++ indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft)
        (assignmentVisitedSymbol value ::
          assignmentTail.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [hleftLayout]
    unfold assignmentRight
    exact step_lookupSkipCertificate_assignment_keepLeft
      formulaValue clauseValue positive value returnMarkers indexEnd
      (List.replicate visited.length indexSpent ++ indexSpent ::
        List.replicate indexTail indexLive ++ processed :: baseLeft)
      (assignmentTail.map assignmentSymbol ++ suffix.map ofBool)
      hreturnMarkers_ne
  have hreturn := run_keepLeft_markers
    (lookupReturnIndex formulaValue clauseValue positive)
    lookupReturnIndexMarker returnMarkers indexEnd
    (List.replicate visited.length indexSpent ++ indexSpent ::
      List.replicate indexTail indexLive ++ processed :: baseLeft)
    (assignmentVisitedSymbol value ::
      assignmentTail.map assignmentSymbol ++ suffix.map ofBool)
    (step_lookupReturnIndex_marker formulaValue clauseValue positive)
    (lookupReturnIndexMarkers_all variableCount visited restLiteralPayload restPayload)
  have hreturn' :
      satControl.run returnMarkers.length
        (keepLeftScanConfig (lookupReturnIndex formulaValue clauseValue positive)
          returnMarkers indexEnd
          (List.replicate visited.length indexSpent ++ indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft)
          (assignmentVisitedSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt (lookupReturnIndex formulaValue clauseValue positive) blank
        (List.replicate visited.length indexSpent ++ indexSpent ::
          List.replicate indexTail indexLive ++ processed :: baseLeft)
        (indexEnd :: (returnMarkers.reverse ++
          (assignmentVisitedSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool))) := by
    simpa only [List.cons_append] using hreturn
  have hend :
      satControl.run 1
        (configAt (lookupReturnIndex formulaValue clauseValue positive) blank
          (List.replicate visited.length indexSpent ++ indexSpent ::
            List.replicate indexTail indexLive ++ processed :: baseLeft)
          (indexEnd :: (returnMarkers.reverse ++
            (assignmentVisitedSymbol value ::
              assignmentTail.map assignmentSymbol ++ suffix.map ofBool)))) =
      keepLeftScanConfig (lookupSelect formulaValue clauseValue positive)
        (List.replicate (visited.length + 1) indexSpent)
        (if indexTail = 0 then processed else indexLive)
        (if indexTail = 0 then baseLeft
          else List.replicate (indexTail - 1) indexLive ++ processed :: baseLeft)
        (indexEnd :: (returnMarkers.reverse ++
          (assignmentVisitedSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool))) := by
    cases indexTail with
    | zero =>
        simpa only [Nat.zero_eq, if_true, Nat.zero_sub, List.replicate_zero,
          List.nil_append, List.append_nil, replicate_cons_same, List.cons_append] using
          (step_lookupReturnIndex_indexEnd_keepLeft
            formulaValue clauseValue positive
            (List.replicate (visited.length + 1) indexSpent)
            processed baseLeft
            (returnMarkers.reverse ++
              (assignmentVisitedSymbol value ::
                assignmentTail.map assignmentSymbol ++ suffix.map ofBool))
            (by simp))
    | succ k =>
        simpa only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one,
          replicate_cons_same, List.replicate_succ, List.cons_append,
          List.append_assoc] using
          (step_lookupReturnIndex_indexEnd_keepLeft
            formulaValue clauseValue positive
            (List.replicate (visited.length + 1) indexSpent)
            indexLive
            (List.replicate k indexLive ++ processed :: baseLeft)
            (returnMarkers.reverse ++
              (assignmentVisitedSymbol value ::
                assignmentTail.map assignmentSymbol ++ suffix.map ofBool))
            (by simp))
  have hspent :
      satControl.run (visited.length + 1)
        (keepLeftScanConfig (lookupSelect formulaValue clauseValue positive)
          (List.replicate (visited.length + 1) indexSpent)
          (if indexTail = 0 then processed else indexLive)
          (if indexTail = 0 then baseLeft
            else List.replicate (indexTail - 1) indexLive ++ processed :: baseLeft)
          (indexEnd :: (returnMarkers.reverse ++
            (assignmentVisitedSymbol value ::
              assignmentTail.map assignmentSymbol ++ suffix.map ofBool)))) =
      lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals (visited ++ [value]) indexTail
        restLiteralPayload restPayload assignmentTail suffix := by
    have hscan := run_keepLeft_markers
      (lookupSelect formulaValue clauseValue positive)
      (fun marker => marker = indexSpent)
      (List.replicate (visited.length + 1) indexSpent)
      (if indexTail = 0 then processed else indexLive)
      (if indexTail = 0 then baseLeft
        else List.replicate (indexTail - 1) indexLive ++ processed :: baseLeft)
      (indexEnd :: (returnMarkers.reverse ++
        (assignmentVisitedSymbol value ::
          assignmentTail.map assignmentSymbol ++ suffix.map ofBool)))
      (by
        intro marker hm leftHead leftTail right
        subst marker
        exact step_lookupSelect_spent formulaValue clauseValue positive
          leftHead leftTail right)
      (by simp)
    rw [List.length_replicate] at hscan
    rw [hscan]
    unfold lookupLoopConfig baseLeft
    unfold returnMarkers
    rw [lookupReturnIndexMarkers_reverse]
    cases indexTail with
    | zero =>
        simp [assignmentVisitedSymbol, List.map_append,
          zeroLookupCertificateMarkers, List.append_assoc]
    | succ k =>
        simp [assignmentVisitedSymbol, List.map_append,
          zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
  have hlenRight : rightMarkers.length =
      visited.length + 1 + restLiteralPayload.length + restPayload.length := by
    exact lookupSkipRightMarkers_length _ _ _
  have hlenCert : certMarkers.length = variableCount + 1 + visited.length := by
    exact lookupSkipCertificateMarkers_length _ _
  have hlenReturn : returnMarkers.length =
      visited.length + variableCount + restLiteralPayload.length + restPayload.length + 2 := by
    exact lookupReturnIndexMarkers_length _ _ _ _
  rw [show 4 * visited.length + 2 * variableCount +
      2 * (restLiteralPayload.length + restPayload.length) + 9 =
      1 + (rightMarkers.length + (1 + (certMarkers.length +
        (1 + (returnMarkers.length + (1 + (visited.length + 1))))))) by omega]
  rw [controlMachine_run_add, hselect]
  rw [controlMachine_run_add, hright]
  rw [controlMachine_run_add, hsep]
  rw [controlMachine_run_add, hcert]
  rw [controlMachine_run_add, hvalue]
  rw [controlMachine_run_add, hreturn']
  rw [controlMachine_run_add, hend]
  exact hspent



/-- Generic exact left scan that may rewrite each crossed marker. -/
theorem run_mapLeft_markers
    (q : SATMachineState)
    (P : SATMachineSymbol → Prop)
    (rewriteMarker : SATMachineSymbol → SATMachineSymbol)
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (hstep : ∀ marker, P marker → ∀ leftHead leftTail r,
      satControl.stepConfig
        (configAt q blank (leftHead :: leftTail) (marker :: r)) =
      configAt q blank leftTail (leftHead :: rewriteMarker marker :: r))
    (hmarkers : ∀ marker ∈ markers, P marker) :
    satControl.run markers.length
      (keepLeftScanConfig q markers baseHead baseLeft right) =
    configAt q blank baseLeft
      (baseHead :: (markers.map rewriteMarker).reverse ++ right) := by
  induction markers generalizing right with
  | nil => rfl
  | cons marker markers ih =>
      change satControl.run (markers.length + 1)
        (configAt q blank (markers ++ baseHead :: baseLeft) (marker :: right)) = _
      change satControl.run markers.length
        (satControl.stepConfig
          (configAt q blank (markers ++ baseHead :: baseLeft) (marker :: right))) = _
      have hm : P marker := hmarkers marker (by simp)
      cases markers with
      | nil =>
          simp only [List.nil_append]
          rw [hstep marker hm baseHead baseLeft right]
          rfl
      | cons next rest =>
          rw [List.cons_append]
          rw [hstep marker hm next (rest ++ baseHead :: baseLeft) right]
          have htail : ∀ m ∈ (next :: rest), P m := by
            intro m hmem
            exact hmarkers m (by simp [hmem])
          have hrec := ih (right := rewriteMarker marker :: right) htail
          have hrec' :
              satControl.run (List.length (next :: rest))
                (configAt q blank (rest ++ baseHead :: baseLeft)
                  (next :: rewriteMarker marker :: right)) =
              configAt q blank baseLeft
                (baseHead :: (List.map rewriteMarker (next :: rest)).reverse ++
                  rewriteMarker marker :: right) := by
            simpa [keepLeftScanConfig] using hrec
          rw [hrec']
          simp [List.reverse_cons, List.map_cons, List.append_assoc]

/-- Restore a visited assignment marker while leaving every other return-path
marker unchanged. -/
def cleanupReturnRewrite (symbol : SATMachineSymbol) : SATMachineSymbol :=
  if symbol = assignmentVisitedFalse then assignmentFalse
  else if symbol = assignmentVisitedTrue then assignmentTrue
  else symbol

@[simp] theorem cleanupReturnRewrite_visitedFalse :
    cleanupReturnRewrite assignmentVisitedFalse = assignmentFalse := by
  rfl

@[simp] theorem cleanupReturnRewrite_visitedTrue :
    cleanupReturnRewrite assignmentVisitedTrue = assignmentTrue := by
  rfl

@[simp] theorem cleanupReturnRewrite_assignmentVisitedSymbol (bit : Bool) :
    cleanupReturnRewrite (assignmentVisitedSymbol bit) = assignmentSymbol bit := by
  cases bit <;> rfl

@[simp] theorem cleanupReturnRewrite_ofBool (bit : Bool) :
    cleanupReturnRewrite (ofBool bit) = ofBool bit := by
  cases bit <;> rfl

@[simp] theorem cleanupReturnRewrite_separator :
    cleanupReturnRewrite separator = separator := by rfl

@[simp] theorem cleanupReturnRewrite_assignmentLengthChecked :
    cleanupReturnRewrite assignmentLengthChecked = assignmentLengthChecked := by rfl

@[simp] theorem cleanupReturnRewrite_assignmentLengthEnd :
    cleanupReturnRewrite assignmentLengthEnd = assignmentLengthEnd := by rfl

@[simp] theorem step_cleanupReturn_lookupMarker
    (formulaValue clauseValue literalValue : Bool)
    (symbol : SATMachineSymbol)
    (h : lookupReturnIndexMarker symbol)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (cleanupReturn formulaValue clauseValue literalValue) blank
        (leftHead :: leftTail) (symbol :: right)) =
    configAt (cleanupReturn formulaValue clauseValue literalValue) blank leftTail
      (leftHead :: cleanupReturnRewrite symbol :: right) := by
  rcases h with rfl | rfl | hcert | rfl | ⟨bit, rfl⟩
  · cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl
  · rcases hcert with rfl | rfl <;>
      cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl
  · cases bit <;> cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl

@[simp] theorem cleanupReturnRewrite_lookupReturnIndexMarkers_reverse
    (variableCount : Nat) (visited : BitString)
    (restLiteralPayload restPayload : BitString) :
    ((lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload).map
      cleanupReturnRewrite).reverse =
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        zeroLookupCertificateMarkers variableCount ++ visited.map assignmentSymbol := by
  unfold lookupReturnIndexMarkers zeroLookupCertificateMarkers
  simp [Function.comp_def, List.reverse_append, List.append_assoc]

/-- Target lookup crosses spent unary-index markers in addition to the raw
literal/formula payload crossed by the zero-index path. -/
@[simp] theorem step_lookupTargetRight_lookupMarker
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol)
    (h : lookupSkipRightMarker symbol)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupTargetRight formulaValue clauseValue positive) blank left
        (symbol :: right)) =
    configAt (lookupTargetRight formulaValue clauseValue positive) blank
      (symbol :: left) right := by
  rcases h with rfl | hzero
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · rcases hzero with rfl | ⟨bit, rfl⟩
    · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
    · cases bit <;> cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Target-certificate lookup also skips previously visited assignment markers. -/
@[simp] theorem step_lookupTargetCertificate_lookupMarker
    (formulaValue clauseValue positive : Bool)
    (symbol : SATMachineSymbol)
    (h : lookupSkipCertificateMarker symbol)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank left
        (symbol :: right)) =
    configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
      (symbol :: left) right := by
  rcases h with hcert | rfl | rfl
  · rcases hcert with rfl | rfl <;>
      cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl
  · cases formulaValue <;> cases clauseValue <;> cases positive <;> rfl

/-- Package the target assignment read as a left-moving cleanup scan. -/
theorem step_lookupTargetCertificate_assignment_keepLeft
    (formulaValue clauseValue positive value : Bool)
    (markers : List SATMachineSymbol) (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (hne : markers ≠ []) :
    satControl.run 1
      (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
        (markers ++ baseHead :: baseLeft) (assignmentSymbol value :: right)) =
    keepLeftScanConfig
      (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
      markers baseHead baseLeft (assignmentSymbol value :: right) := by
  rw [controlMachine_run_one]
  cases markers with
  | nil => exact (hne rfl).elim
  | cons marker remaining =>
      simp only [List.cons_append]
      rw [step_lookupTargetCertificate_assignment]
      rfl

@[simp] theorem step_cleanupIndex_spent
    (formulaValue clauseValue literalValue : Bool)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt (cleanupIndex formulaValue clauseValue literalValue) blank
        (leftHead :: leftTail) (indexSpent :: right)) =
    configAt (cleanupIndex formulaValue clauseValue literalValue) blank leftTail
      (leftHead :: processed :: right) := by
  cases formulaValue <;> cases clauseValue <;> cases literalValue <;> rfl

/-- Package the index-terminator cleanup step as the canonical scan over the
spent unary-index markers. -/
theorem step_cleanupReturn_indexEnd_keepLeft
    (formulaValue clauseValue literalValue : Bool)
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol) :
    satControl.run 1
      (configAt (cleanupReturn formulaValue clauseValue literalValue) blank
        (markers ++ baseHead :: baseLeft) (indexEnd :: right)) =
    keepLeftScanConfig (cleanupIndex formulaValue clauseValue literalValue)
      markers baseHead baseLeft (processed :: right) := by
  rw [controlMachine_run_one]
  cases markers with
  | nil =>
      simp [keepLeftScanConfig]
  | cons marker remaining =>
      simp only [List.cons_append]
      rw [step_cleanupReturn_indexEnd]
      rfl

/-- Canonical state after a literal at an arbitrary valid assignment index has
been evaluated and all lookup scratch markers have been cleaned. -/
def literalEvaluatedConfig
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited : BitString)
    (restLiteralPayload restPayload assignmentTail suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt
    (clauseFind formulaValue (clauseValue || applyPolarity positive value)) blank
    (clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank])
    (clauseEnd :: List.replicate (visited.length + 2) processed ++
      restLiteralPayload.map ofBool ++ restPayload.map ofBool ++ separator ::
        List.replicate variableCount assignmentLengthChecked ++
          assignmentLengthEnd :: visited.map assignmentSymbol ++ assignmentSymbol value ::
            assignmentTail.map assignmentSymbol ++ suffix.map ofBool)


/-- General target read. After all live unary index markers have been consumed,
the machine reads the current assignment slot, applies polarity, restores all
previously visited assignment cells, cleans the spent index markers, and returns
to `clauseFind`. -/
theorem run_lookupLoop_target
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (4 * visited.length + 2 * variableCount +
        2 * (restLiteralPayload.length + restPayload.length) + 9)
      (lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited 0
        restLiteralPayload restPayload (value :: assignmentTail) suffix) =
    literalEvaluatedConfig formulaValue clauseValue positive value variableCount
      remainingClauses remainingLiterals visited restLiteralPayload restPayload
      assignmentTail suffix := by
  let baseLeft : List SATMachineSymbol :=
    clauseEnd :: clauseSpent :: List.replicate remainingLiterals clauseLive ++
      formulaEnd :: formulaSpent :: List.replicate remainingClauses formulaLive ++
        variableEnd :: List.replicate variableCount variableChecked ++ [blank]
  let rightMarkers :=
    lookupSkipRightMarkers visited.length restLiteralPayload restPayload
  let certMarkers := lookupSkipCertificateMarkers variableCount visited
  let returnMarkers :=
    lookupReturnIndexMarkers variableCount visited restLiteralPayload restPayload
  let assignmentRight : List SATMachineSymbol :=
    assignmentSymbol value :: assignmentTail.map assignmentSymbol ++ suffix.map ofBool
  have hreturnMarkers_ne : returnMarkers ≠ [] := by
    unfold returnMarkers lookupReturnIndexMarkers zeroLookupCertificateMarkers
    simp
  have hselect :
      satControl.run 1
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited 0
          restLiteralPayload restPayload (value :: assignmentTail) suffix) =
      configAt (lookupTargetRight formulaValue clauseValue positive) blank
        (processed :: baseLeft)
        (rightMarkers ++ (separator :: certMarkers ++ assignmentRight)) := by
    rw [controlMachine_run_one]
    unfold lookupLoopConfig baseLeft rightMarkers certMarkers assignmentRight
    unfold lookupSkipRightMarkers lookupSkipCertificateMarkers
    unfold zeroLookupRightMarkers zeroLookupCertificateMarkers
    cases formulaValue <;> cases clauseValue <;> cases positive <;> cases value <;>
      simp [List.append_assoc]
    all_goals rfl
  have hright := run_keepRight_markers
    (lookupTargetRight formulaValue clauseValue positive)
    lookupSkipRightMarker rightMarkers (processed :: baseLeft)
    (separator :: certMarkers ++ assignmentRight)
    (step_lookupTargetRight_lookupMarker formulaValue clauseValue positive)
    (lookupSkipRightMarkers_all visited.length restLiteralPayload restPayload)
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
    lookupSkipCertificateMarker certMarkers
    (separator :: rightMarkers.reverse ++ processed :: baseLeft)
    assignmentRight
    (step_lookupTargetCertificate_lookupMarker formulaValue clauseValue positive)
    (lookupSkipCertificateMarkers_all variableCount visited)
  have hleftLayout :
      certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ processed :: baseLeft) =
      returnMarkers ++ indexEnd ::
        (List.replicate visited.length indexSpent ++ processed :: baseLeft) := by
    unfold certMarkers rightMarkers returnMarkers
    unfold lookupSkipCertificateMarkers lookupSkipRightMarkers
    unfold lookupReturnIndexMarkers zeroLookupCertificateMarkers zeroLookupRightMarkers
    simp [List.reverse_append, List.append_assoc]
  have hvalue :
      satControl.run 1
        (configAt (lookupTargetCertificate formulaValue clauseValue positive) blank
          (certMarkers.reverse ++ (separator :: rightMarkers.reverse ++ processed :: baseLeft))
          assignmentRight) =
      keepLeftScanConfig
        (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
        returnMarkers indexEnd
        (List.replicate visited.length indexSpent ++ processed :: baseLeft)
        assignmentRight := by
    rw [hleftLayout]
    exact step_lookupTargetCertificate_assignment_keepLeft
      formulaValue clauseValue positive value returnMarkers indexEnd
      (List.replicate visited.length indexSpent ++ processed :: baseLeft)
      (assignmentTail.map assignmentSymbol ++ suffix.map ofBool)
      hreturnMarkers_ne
  have hreturn := run_mapLeft_markers
    (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
    lookupReturnIndexMarker cleanupReturnRewrite returnMarkers indexEnd
    (List.replicate visited.length indexSpent ++ processed :: baseLeft)
    assignmentRight
    (step_cleanupReturn_lookupMarker formulaValue clauseValue
      (applyPolarity positive value))
    (lookupReturnIndexMarkers_all variableCount visited restLiteralPayload restPayload)
  have hreturn' :
      satControl.run returnMarkers.length
        (keepLeftScanConfig
          (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
          returnMarkers indexEnd
          (List.replicate visited.length indexSpent ++ processed :: baseLeft)
          assignmentRight) =
      configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
        blank (List.replicate visited.length indexSpent ++ processed :: baseLeft)
        (indexEnd :: ((returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)) := by
    simpa only [List.cons_append] using hreturn
  have hindexEnd :
      satControl.run 1
        (configAt (cleanupReturn formulaValue clauseValue (applyPolarity positive value))
          blank (List.replicate visited.length indexSpent ++ processed :: baseLeft)
          (indexEnd :: ((returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight))) =
      keepLeftScanConfig
        (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
        (List.replicate visited.length indexSpent) processed baseLeft
        (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight) := by
    exact step_cleanupReturn_indexEnd_keepLeft
      formulaValue clauseValue (applyPolarity positive value)
      (List.replicate visited.length indexSpent) processed baseLeft
      ((returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)
  have hspent := run_mapLeft_markers
    (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
    (fun marker => marker = indexSpent)
    (fun _ => processed)
    (List.replicate visited.length indexSpent) processed baseLeft
    (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_cleanupIndex_spent formulaValue clauseValue
        (applyPolarity positive value) leftHead leftTail right)
    (by simp)
  have hspent' :
      satControl.run visited.length
        (keepLeftScanConfig (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
          (List.replicate visited.length indexSpent) processed baseLeft
          (processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)) =
      configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive value)) blank baseLeft
        (processed ::
          ((List.replicate visited.length indexSpent).map (fun _ => processed)).reverse ++
            processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight) := by
    simpa using hspent
  have hclean :
      satControl.run 1
        (configAt (cleanupIndex formulaValue clauseValue (applyPolarity positive value))
          blank baseLeft
          (processed ::
            ((List.replicate visited.length indexSpent).map (fun _ => processed)).reverse ++
              processed :: (returnMarkers.map cleanupReturnRewrite).reverse ++ assignmentRight)) =
      literalEvaluatedConfig formulaValue clauseValue positive value variableCount
        remainingClauses remainingLiterals visited restLiteralPayload restPayload
        assignmentTail suffix := by
    rw [controlMachine_run_one]
    unfold baseLeft
    simp only [List.cons_append]
    rw [step_cleanupIndex_processed]
    unfold literalEvaluatedConfig assignmentRight returnMarkers
    simp [cleanupReturnRewrite_lookupReturnIndexMarkers_reverse,
      zeroLookupCertificateMarkers, List.replicate_succ, List.append_assoc]
  have hlenRight : rightMarkers.length =
      visited.length + 1 + restLiteralPayload.length + restPayload.length := by
    exact lookupSkipRightMarkers_length _ _ _
  have hlenCert : certMarkers.length = variableCount + 1 + visited.length := by
    exact lookupSkipCertificateMarkers_length _ _
  have hlenReturn : returnMarkers.length =
      visited.length + variableCount + restLiteralPayload.length + restPayload.length + 2 := by
    exact lookupReturnIndexMarkers_length _ _ _ _
  rw [show 4 * visited.length + 2 * variableCount +
      2 * (restLiteralPayload.length + restPayload.length) + 9 =
      1 + (rightMarkers.length + (1 + (certMarkers.length +
        (1 + (returnMarkers.length + (1 + (visited.length + 1))))))) by omega]
  rw [controlMachine_run_add, hselect]
  rw [controlMachine_run_add, hright]
  rw [controlMachine_run_add, hsep]
  rw [controlMachine_run_add, hcert]
  rw [controlMachine_run_add, hvalue]
  rw [controlMachine_run_add, hreturn']
  rw [controlMachine_run_add, hindexEnd]
  rw [controlMachine_run_add, hspent']
  exact hclean

/-- Exact cost of one indexed assignment-slot skip at a given visited-prefix
length. -/
def lookupSkipOneCost
    (visitedCount variableCount restLiteralLength restPayloadLength : Nat) : Nat :=
  4 * visitedCount + 2 * variableCount +
    2 * (restLiteralLength + restPayloadLength) + 9

/-- Exact accumulated cost for skipping `count` assignment slots, starting
with `visitedCount` slots already marked visited. -/
def lookupSkipCostFrom
    (visitedCount variableCount restLiteralLength restPayloadLength : Nat) :
    Nat → Nat
  | 0 => 0
  | count + 1 =>
      lookupSkipOneCost visitedCount variableCount restLiteralLength restPayloadLength +
        lookupSkipCostFrom (visitedCount + 1) variableCount
          restLiteralLength restPayloadLength count

/-- Repeated indexed skip theorem. A unary literal index represented by
`skipped.length` live markers skips exactly the corresponding assignment prefix,
leaving the selector at the processed sign marker with the skipped assignment
values recorded as visited markers. -/
theorem run_lookupLoop_prefix
    (formulaValue clauseValue positive : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (visited skipped restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (lookupSkipCostFrom visited.length variableCount restLiteralPayload.length
        restPayload.length skipped.length)
      (lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals visited skipped.length
        restLiteralPayload restPayload (skipped ++ assignmentTail) suffix) =
    lookupLoopConfig formulaValue clauseValue positive variableCount
      remainingClauses remainingLiterals (visited ++ skipped) 0
      restLiteralPayload restPayload assignmentTail suffix := by
  induction skipped generalizing visited with
  | nil =>
      simp [lookupSkipCostFrom, lookupLoopConfig]
  | cons value rest ih =>
      change satControl.run
        (lookupSkipOneCost visited.length variableCount restLiteralPayload.length
            restPayload.length +
          lookupSkipCostFrom (visited.length + 1) variableCount
            restLiteralPayload.length restPayload.length rest.length)
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals visited (rest.length + 1)
          restLiteralPayload restPayload (value :: (rest ++ assignmentTail)) suffix) = _
      rw [controlMachine_run_add]
      have hone := run_lookupLoop_one
        formulaValue clauseValue positive value variableCount remainingClauses
        remainingLiterals rest.length visited restLiteralPayload restPayload
        (rest ++ assignmentTail) suffix
      have hone' :
          satControl.run
            (lookupSkipOneCost visited.length variableCount restLiteralPayload.length
              restPayload.length)
            (lookupLoopConfig formulaValue clauseValue positive variableCount
              remainingClauses remainingLiterals visited (rest.length + 1)
              restLiteralPayload restPayload (value :: (rest ++ assignmentTail)) suffix) =
          lookupLoopConfig formulaValue clauseValue positive variableCount
            remainingClauses remainingLiterals (visited ++ [value]) rest.length
            restLiteralPayload restPayload (rest ++ assignmentTail) suffix := by
        simpa [lookupSkipOneCost] using hone
      rw [hone']
      have hrest := ih (visited := visited ++ [value])
      simpa [List.append_assoc] using hrest


/-- Exact total cost of a valid literal lookup at unary assignment index
`index`: skip the preceding slots, then read and clean the target slot. -/
def literalLookupCost
    (variableCount restLiteralLength restPayloadLength index : Nat) : Nat :=
  lookupSkipCostFrom 0 variableCount restLiteralLength restPayloadLength index +
    lookupSkipOneCost index variableCount restLiteralLength restPayloadLength

/-- Full arbitrary-index literal lookup. `skipped` is exactly the assignment
prefix preceding the target value, so its length is the unary variable index.
The machine returns to `clauseFind` with the correct polarity-adjusted literal
value accumulated into the clause state and the entire assignment restored. -/
theorem run_literalLookup_valid
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (literalLookupCost variableCount restLiteralPayload.length
        restPayload.length skipped.length)
      (literalLookupSelectConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals skipped.length
        restLiteralPayload restPayload (skipped ++ value :: assignmentTail) suffix) =
    literalEvaluatedConfig formulaValue clauseValue positive value variableCount
      remainingClauses remainingLiterals skipped restLiteralPayload restPayload
      assignmentTail suffix := by
  have hstart := literalLookupSelectConfig_eq_lookupLoopConfig
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals skipped.length restLiteralPayload restPayload
    (skipped ++ value :: assignmentTail) suffix
  have hskip := run_lookupLoop_prefix
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals ([] : BitString) skipped restLiteralPayload restPayload
    (value :: assignmentTail) suffix
  have htarget := run_lookupLoop_target
    formulaValue clauseValue positive value variableCount remainingClauses
    remainingLiterals skipped restLiteralPayload restPayload assignmentTail suffix
  have hskip' :
      satControl.run
        (lookupSkipCostFrom 0 variableCount restLiteralPayload.length
          restPayload.length skipped.length)
        (lookupLoopConfig formulaValue clauseValue positive variableCount
          remainingClauses remainingLiterals [] skipped.length
          restLiteralPayload restPayload (skipped ++ value :: assignmentTail) suffix) =
      lookupLoopConfig formulaValue clauseValue positive variableCount
        remainingClauses remainingLiterals skipped 0 restLiteralPayload restPayload
        (value :: assignmentTail) suffix := by
    simpa using hskip
  unfold literalLookupCost
  rw [controlMachine_run_add]
  rw [hstart]
  rw [hskip']
  simpa [lookupSkipOneCost] using htarget


/-- Exact end-to-end cost from a canonical literal sign bit through unary index
decoding, arbitrary assignment lookup, polarity application, restoration, and
return to `clauseFind`. -/
def literalEvaluationCost
    (variableCount restLiteralLength restPayloadLength index : Nat) : Nat :=
  index + 2 + literalLookupCost variableCount restLiteralLength restPayloadLength index

/-- End-to-end semantics for one canonically encoded literal at any valid
assignment index. -/
theorem run_literal_valid
    (formulaValue clauseValue positive value : Bool)
    (variableCount remainingClauses remainingLiterals : Nat)
    (skipped restLiteralPayload restPayload assignmentTail suffix : BitString) :
    satControl.run
      (literalEvaluationCost variableCount restLiteralPayload.length
        restPayload.length skipped.length)
      (firstLiteralSignConfig formulaValue clauseValue variableCount
        remainingClauses remainingLiterals
        (positive :: List.replicate skipped.length true ++ [false])
        restLiteralPayload restPayload (skipped ++ value :: assignmentTail) suffix) =
    literalEvaluatedConfig formulaValue clauseValue positive value variableCount
      remainingClauses remainingLiterals skipped restLiteralPayload restPayload
      assignmentTail suffix := by
  have hparse := run_literal_to_lookupSelect
    formulaValue clauseValue positive variableCount remainingClauses
    remainingLiterals skipped.length restLiteralPayload restPayload
    (skipped ++ value :: assignmentTail) suffix
  have hlookup := run_literalLookup_valid
    formulaValue clauseValue positive value variableCount remainingClauses
    remainingLiterals skipped restLiteralPayload restPayload assignmentTail suffix
  unfold literalEvaluationCost
  rw [controlMachine_run_add, hparse]
  exact hlookup

end SATMachineCertificatePhase
end OpenProblems.Complexity
