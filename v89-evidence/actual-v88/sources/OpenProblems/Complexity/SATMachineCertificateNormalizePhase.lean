import OpenProblems.Complexity.SATMachinePairingPhase

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState

@[simp] theorem step_findLive_separator
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt certificateFindLive blank left (separator :: right)) =
    configAt certificateNormalize blank (separator :: left) right := by
  cases right <;> rfl

@[simp] theorem step_normalize_spent
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt certificateNormalize blank left (assignmentLengthSpent :: right)) =
    configAt certificateNormalize blank (assignmentLengthCount :: left) right := by
  rfl

/-- Convert all spent unary length markers into checked count markers. -/
theorem run_normalize_spent
    (n : Nat) (left payload : List SATMachineSymbol) :
    satControl.run n
      (configAt certificateNormalize blank left
        (List.replicate n assignmentLengthSpent ++ payload)) =
    configAt certificateNormalize blank
      (List.replicate n assignmentLengthCount ++ left) payload := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change satControl.run n
        (satControl.stepConfig
          (configAt certificateNormalize blank left
            ((assignmentLengthSpent :: List.replicate n assignmentLengthSpent) ++ payload))) = _
      have hstep :
          satControl.stepConfig
            (configAt certificateNormalize blank left
              ((assignmentLengthSpent :: List.replicate n assignmentLengthSpent) ++ payload)) =
          configAt certificateNormalize blank
            (assignmentLengthCount :: left)
            (List.replicate n assignmentLengthSpent ++ payload) := by
        exact step_normalize_spent left
          (List.replicate n assignmentLengthSpent ++ payload)
      rw [hstep, ih]
      have hrep :
          List.replicate n assignmentLengthCount ++ assignmentLengthCount :: left =
            List.replicate (n + 1) assignmentLengthCount ++ left :=
        replicate_append_same_marker n assignmentLengthCount left
      rw [hrep, List.replicate_succ]

@[simp] theorem step_normalize_end
    (leftHead : SATMachineSymbol)
    (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt certificateNormalize blank (leftHead :: leftTail)
        (assignmentLengthEnd :: right)) =
    configAt returnLeft blank leftTail
      (leftHead :: assignmentLengthEnd :: right) := by
  rfl

/-- Symbols traversed on the leftward return to the initial blank. -/
def returnMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = assignmentLengthCount ∨ symbol = separator ∨
    symbol = rawFalse ∨ symbol = rawTrue

@[simp] theorem returnMarker_count : returnMarker assignmentLengthCount := Or.inl rfl
@[simp] theorem returnMarker_separator : returnMarker separator := Or.inr (Or.inl rfl)
@[simp] theorem returnMarker_ofBool (bit : Bool) : returnMarker (ofBool bit) := by
  cases bit <;> simp [returnMarker, ofBool]

def returnLeftScanConfig
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol) :
    Config SATMachineState SATMachineSymbol :=
  match markers with
  | [] => configAt returnLeft blank baseLeft (baseHead :: right)
  | marker :: remaining =>
      configAt returnLeft blank
        (remaining ++ baseHead :: baseLeft) (marker :: right)

@[simp] theorem step_returnLeft_marker
    (leftHead marker : SATMachineSymbol)
    (leftTail right : List SATMachineSymbol)
    (hmarker : returnMarker marker) :
    satControl.stepConfig
      (configAt returnLeft blank (leftHead :: leftTail) (marker :: right)) =
    configAt returnLeft blank leftTail (leftHead :: marker :: right) := by
  rcases hmarker with rfl | rfl | rfl | rfl <;> rfl

/-- Exact left scan across any generated return-marker block. -/
theorem run_returnLeft_markers
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (hmarkers : ∀ marker ∈ markers, returnMarker marker) :
    satControl.run markers.length
      (returnLeftScanConfig markers baseHead baseLeft right) =
    configAt returnLeft blank baseLeft
      (baseHead :: markers.reverse ++ right) := by
  induction markers generalizing right with
  | nil => rfl
  | cons marker markers ih =>
      change satControl.run (markers.length + 1)
        (configAt returnLeft blank
          (markers ++ baseHead :: baseLeft) (marker :: right)) = _
      change satControl.run markers.length
        (satControl.stepConfig
          (configAt returnLeft blank
            (markers ++ baseHead :: baseLeft) (marker :: right))) = _
      have hm : returnMarker marker := hmarkers marker (by simp)
      cases markers with
      | nil =>
          simp only [List.nil_append]
          rw [step_returnLeft_marker baseHead marker baseLeft right hm]
          rfl
      | cons next rest =>
          rw [List.cons_append]
          rw [step_returnLeft_marker next marker
            (rest ++ baseHead :: baseLeft) right hm]
          have htail : ∀ m ∈ (next :: rest), returnMarker m := by
            intro m hmemb
            exact hmarkers m (by simp [hmemb])
          have hrec := ih (right := marker :: right) htail
          have hrec' :
              satControl.run (List.length (next :: rest))
                (configAt returnLeft blank
                  (rest ++ baseHead :: baseLeft) (next :: marker :: right)) =
              configAt returnLeft blank baseLeft
                (baseHead :: (next :: rest).reverse ++ marker :: right) := by
            simpa [returnLeftScanConfig] using hrec
          rw [hrec']
          simp [List.reverse_cons, List.append_assoc]

@[simp] theorem step_returnLeft_blank
    (right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt returnLeft blank [] (blank :: right)) =
    configAt variableLength blank [blank] right := by
  cases right <;> rfl

/-- Complete marker block crossed after certificate normalization. -/
def normalizedReturnMarkers
    (input : BitString) (assignmentLength : Nat) : List SATMachineSymbol :=
  List.replicate assignmentLength assignmentLengthCount ++
    separator :: (input.map ofBool).reverse

@[simp] theorem normalizedReturnMarkers_length
    (input : BitString) (assignmentLength : Nat) :
    (normalizedReturnMarkers input assignmentLength).length =
      assignmentLength + 1 + input.length := by
  simp [normalizedReturnMarkers]
  omega

@[simp] theorem normalizedReturnMarkers_reverse
    (input : BitString) (assignmentLength : Nat) :
    (normalizedReturnMarkers input assignmentLength).reverse =
      input.map ofBool ++ separator ::
        List.replicate assignmentLength assignmentLengthCount := by
  simp [normalizedReturnMarkers, List.reverse_append, List.append_assoc]

theorem returnMarker_mem_normalizedReturnMarkers
    (input : BitString) (assignmentLength : Nat)
    (marker : SATMachineSymbol)
    (hmem : marker ∈ normalizedReturnMarkers input assignmentLength) :
    returnMarker marker := by
  unfold normalizedReturnMarkers at hmem
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hmem
  rcases hmem with hcount | hsep | hinput
  · rcases hcount with ⟨_, rfl⟩
    exact returnMarker_count
  · subst marker
    exact returnMarker_separator
  · have hinput' : marker ∈ input.map ofBool := by
      simpa using List.mem_reverse.mp hinput
    rcases List.mem_map.mp hinput' with ⟨bit, _, rfl⟩
    exact returnMarker_ofBool bit

/-- Canonical state at the beginning of the variable-count comparison phase. -/
def variableLengthEntryConfig
    (input assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt variableLength blank [blank]
    (input.map ofBool ++ separator ::
      List.replicate assignment.length assignmentLengthCount ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++
          suffix.map ofBool)

/-- Fully paired canonical certificate returns to the variable-length phase. -/
theorem run_fullyPaired_to_variableLength
    (input assignment suffix : BitString) :
    satControl.run (2 * assignment.length + input.length + 4)
      (pairingConfig
        ((input.map ofBool).reverse ++ [blank])
        assignment [] suffix) =
    variableLengthEntryConfig input assignment suffix := by
  let markers := normalizedReturnMarkers input assignment.length
  have hmarkers : ∀ marker ∈ markers, returnMarker marker := by
    intro marker hmem
    exact returnMarker_mem_normalizedReturnMarkers input assignment.length marker hmem
  have hstart :
      satControl.run 1
        (pairingConfig
          ((input.map ofBool).reverse ++ [blank])
          assignment [] suffix) =
      configAt certificateNormalize blank
        (separator :: (input.map ofBool).reverse ++ [blank])
        (List.replicate assignment.length assignmentLengthSpent ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    change satControl.stepConfig
      (configAt certificateFindLive blank
        ((input.map ofBool).reverse ++ [blank])
        (separator :: List.replicate assignment.length assignmentLengthSpent ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) = _
    simpa [List.append_assoc] using
      (step_findLive_separator ((input.map ofBool).reverse ++ [blank])
        (List.replicate assignment.length assignmentLengthSpent ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool))
  have hnormalize := run_normalize_spent assignment.length
    (separator :: (input.map ofBool).reverse ++ [blank])
    (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
  have hnormalized :
      satControl.run (1 + assignment.length)
        (pairingConfig
          ((input.map ofBool).reverse ++ [blank])
          assignment [] suffix) =
      configAt certificateNormalize blank
        (List.replicate assignment.length assignmentLengthCount ++
          separator :: (input.map ofBool).reverse ++ [blank])
        (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hstart]
    simpa [List.append_assoc] using hnormalize
  have hend :
      satControl.run 1
        (configAt certificateNormalize blank
          (List.replicate assignment.length assignmentLengthCount ++
            separator :: (input.map ofBool).reverse ++ [blank])
          (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      returnLeftScanConfig markers blank []
        (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    unfold markers normalizedReturnMarkers returnLeftScanConfig
    cases hcount : List.replicate assignment.length assignmentLengthCount with
    | nil =>
        simp only [hcount, List.nil_append]
        have hstep := step_normalize_end separator
          ((input.map ofBool).reverse ++ [blank])
          (assignment.map assignmentSymbol ++ suffix.map ofBool)
        simpa [List.append_assoc] using hstep
    | cons marker rest =>
        simp only [hcount, List.cons_append]
        have hstep := step_normalize_end marker
          (rest ++ separator :: (input.map ofBool).reverse ++ [blank])
          (assignment.map assignmentSymbol ++ suffix.map ofBool)
        simpa [List.append_assoc] using hstep
  have hscan := run_returnLeft_markers markers blank []
    (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) hmarkers
  have hblank :
      satControl.run 1
        (configAt returnLeft blank []
          (blank :: markers.reverse ++ assignmentLengthEnd ::
            assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt variableLength blank [blank]
        (markers.reverse ++ assignmentLengthEnd ::
          assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    simpa [List.append_assoc] using
      (step_returnLeft_blank
        (markers.reverse ++ assignmentLengthEnd ::
          assignment.map assignmentSymbol ++ suffix.map ofBool))
  have hfull :
      satControl.run (((1 + assignment.length) + 1) + markers.length + 1)
        (pairingConfig
          ((input.map ofBool).reverse ++ [blank])
          assignment [] suffix) =
      configAt variableLength blank [blank]
        (markers.reverse ++ assignmentLengthEnd ::
          assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, controlMachine_run_add, controlMachine_run_add]
    rw [hnormalized, hend, hscan]
    simpa [List.append_assoc] using hblank
  rw [show 2 * assignment.length + input.length + 4 =
      ((1 + assignment.length) + 1) + markers.length + 1 by
    simp [markers, normalizedReturnMarkers]
    omega]
  rw [hfull]
  unfold variableLengthEntryConfig markers
  simp [normalizedReturnMarkers_reverse, List.append_assoc]


/-- From the certificate-length state, the full canonical certificate phase has a closed exact cost. -/
theorem run_certificateLength_to_variableLength
    (input assignment suffix : BitString) :
    satControl.run
        (2 * assignment.length * assignment.length +
          6 * assignment.length + input.length + 5)
        (encodedSATCertificateLengthConfig
          (SATMachineSymbol.separator ::
            (input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
          (CNF.encodeAssignment assignment ++ suffix)) =
      variableLengthEntryConfig input assignment suffix := by
  let pairCost := 2 * assignment.length * assignment.length + 3 * assignment.length
  let finishCost := 2 * assignment.length + input.length + 4
  have hprefix := run_encodedAssignment_to_pairing
    ((input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
    assignment suffix
  have hpair := run_pairing_all_from_zero
    ((input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
    assignment suffix
  have hfinish := run_fullyPaired_to_variableLength input assignment suffix
  have hsum :
      2 * assignment.length * assignment.length +
          6 * assignment.length + input.length + 5 =
        ((assignment.length + 1) + pairCost) + finishCost := by
    unfold pairCost finishCost
    omega
  have hprefix' :
      satControl.run (assignment.length + 1)
        (encodedSATCertificateLengthConfig
          (SATMachineSymbol.separator ::
            (input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
          (CNF.encodeAssignment assignment ++ suffix)) =
      pairingConfig
        ((input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
        [] assignment suffix := by
    simpa [List.append_assoc] using hprefix
  have hprefixPair :
      satControl.run ((assignment.length + 1) + pairCost)
        (encodedSATCertificateLengthConfig
          (SATMachineSymbol.separator ::
            (input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
          (CNF.encodeAssignment assignment ++ suffix)) =
      pairingConfig
        ((input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
        assignment [] suffix := by
    rw [controlMachine_run_add, hprefix']
    simpa [pairCost] using hpair
  have hall :
      satControl.run (((assignment.length + 1) + pairCost) + finishCost)
        (encodedSATCertificateLengthConfig
          (SATMachineSymbol.separator ::
            (input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
          (CNF.encodeAssignment assignment ++ suffix)) =
      variableLengthEntryConfig input assignment suffix := by
    rw [controlMachine_run_add, hprefixPair]
    simpa [finishCost] using hfinish
  rw [hsum]
  exact hall

/-- The whole typed prefix from initial input through certificate normalization. -/
theorem run_typed_to_variableLength
    (input assignment suffix : BitString) :
    satControl.run
        (2 * assignment.length * assignment.length +
          6 * assignment.length + 2 * input.length + 7)
        (encodedSATTypedInitialConfig
          input (CNF.encodeAssignment assignment ++ suffix)) =
      variableLengthEntryConfig input assignment suffix := by
  have hinput := encodedSATTyped_run_to_certificateLength
    input (CNF.encodeAssignment assignment ++ suffix)
  have hcertificate := run_certificateLength_to_variableLength
    input assignment suffix
  have hsum :
      2 * assignment.length * assignment.length +
          6 * assignment.length + 2 * input.length + 7 =
        (input.length + 2) +
          (2 * assignment.length * assignment.length +
            6 * assignment.length + input.length + 5) := by
    omega
  have hall :
      satControl.run
        ((input.length + 2) +
          (2 * assignment.length * assignment.length +
            6 * assignment.length + input.length + 5))
        (encodedSATTypedInitialConfig
          input (CNF.encodeAssignment assignment ++ suffix)) =
      variableLengthEntryConfig input assignment suffix := by
    rw [controlMachine_run_add]
    change satControl.run
      (2 * assignment.length * assignment.length +
        6 * assignment.length + input.length + 5)
      (satControl.run (input.length + 2)
        (encodedSATTypedInitialConfig
          input (CNF.encodeAssignment assignment ++ suffix))) = _
    have hinput' :
        satControl.run (input.length + 2)
          (encodedSATTypedInitialConfig
            input (CNF.encodeAssignment assignment ++ suffix)) =
        encodedSATCertificateLengthConfig
          (SATMachineSymbol.separator ::
            (input.map SATMachineSymbol.ofBool).reverse ++ [SATMachineSymbol.blank])
          (CNF.encodeAssignment assignment ++ suffix) := by
      change satControl.run (input.length + 2)
        (encodedSATTypedInitialConfig
          input (CNF.encodeAssignment assignment ++ suffix)) = _ at hinput
      simpa [List.append_assoc] using hinput
    rw [hinput', hcertificate]
  rw [hsum]
  exact hall

/-- Raw finite-machine lowering preserves the complete typed certificate phase. -/
theorem run_raw_to_variableLength
    (input assignment suffix : BitString) :
    encodedSATFiniteMachine.toDTM.run
        (2 * assignment.length * assignment.length +
          6 * assignment.length + 2 * input.length + 7)
        (FiniteControlMachine.encodeConfig
          (encodedSATTypedInitialConfig
            input (CNF.encodeAssignment assignment ++ suffix))) =
      FiniteControlMachine.encodeConfig
        (variableLengthEntryConfig input assignment suffix) := by
  unfold encodedSATFiniteMachine
  calc
    _ = FiniteControlMachine.encodeConfig
        (satControl.run
          (2 * assignment.length * assignment.length +
            6 * assignment.length + 2 * input.length + 7)
          (encodedSATTypedInitialConfig
            input (CNF.encodeAssignment assignment ++ suffix))) :=
      FiniteControlMachine.lowerAbsorbing_run_commutes
        encodedSATFiniteControl
        (2 * assignment.length * assignment.length +
          6 * assignment.length + 2 * input.length + 7)
        (encodedSATTypedInitialConfig
          input (CNF.encodeAssignment assignment ++ suffix))
    _ = _ := congrArg FiniteControlMachine.encodeConfig
      (run_typed_to_variableLength input assignment suffix)

end SATMachineCertificatePhase

end OpenProblems.Complexity
