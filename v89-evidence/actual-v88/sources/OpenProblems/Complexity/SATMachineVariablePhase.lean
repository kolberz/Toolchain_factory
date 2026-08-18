import OpenProblems.Complexity.SATMachineCertificateNormalizePhase
import OpenProblems.Complexity.SATMachineCodecLayout

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState

/-- Generic exact right scan for a control state whose listed markers are all
preserved while the head moves right. -/
theorem run_keepRight_markers
    (q : SATMachineState)
    (P : SATMachineSymbol → Prop)
    (markers : List SATMachineSymbol)
    (left payload : List SATMachineSymbol)
    (hstep : ∀ marker, P marker → ∀ l r,
      satControl.stepConfig (configAt q blank l (marker :: r)) =
        configAt q blank (marker :: l) r)
    (hmarkers : ∀ marker ∈ markers, P marker) :
    satControl.run markers.length
      (configAt q blank left (markers ++ payload)) =
    configAt q blank (markers.reverse ++ left) payload := by
  induction markers generalizing left with
  | nil => rfl
  | cons marker markers ih =>
      rw [List.cons_append]
      change satControl.run markers.length
        (satControl.stepConfig
          (configAt q blank left (marker :: (markers ++ payload)))) = _
      rw [hstep marker (hmarkers marker (by simp)) left (markers ++ payload)]
      have htail : ∀ m ∈ markers, P m := by
        intro m hm
        exact hmarkers m (by simp [hm])
      rw [ih (left := marker :: left) htail]
      simp [List.reverse_cons, List.append_assoc]

/-- Canonical layout for a left-moving scan. `markers` are ordered from the
current head toward `baseHead`. -/
def keepLeftScanConfig
    (q : SATMachineState)
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol) :
    Config SATMachineState SATMachineSymbol :=
  match markers with
  | [] => configAt q blank baseLeft (baseHead :: right)
  | marker :: remaining =>
      configAt q blank (remaining ++ baseHead :: baseLeft) (marker :: right)

/-- Generic exact left scan for a control state whose listed markers are all
preserved while the head moves left. -/
theorem run_keepLeft_markers
    (q : SATMachineState)
    (P : SATMachineSymbol → Prop)
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (hstep : ∀ marker, P marker → ∀ leftHead leftTail r,
      satControl.stepConfig
        (configAt q blank (leftHead :: leftTail) (marker :: r)) =
      configAt q blank leftTail (leftHead :: marker :: r))
    (hmarkers : ∀ marker ∈ markers, P marker) :
    satControl.run markers.length
      (keepLeftScanConfig q markers baseHead baseLeft right) =
    configAt q blank baseLeft (baseHead :: markers.reverse ++ right) := by
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
          have hrec := ih (right := marker :: right) htail
          have hrec' :
              satControl.run (List.length (next :: rest))
                (configAt q blank (rest ++ baseHead :: baseLeft)
                  (next :: marker :: right)) =
              configAt q blank baseLeft
                (baseHead :: (next :: rest).reverse ++ marker :: right) := by
            simpa [keepLeftScanConfig] using hrec
          rw [hrec']
          simp [List.reverse_cons, List.append_assoc]

/-- Symbols crossed while moving from one variable marker to the certificate
separator. -/
def variableToSeparatorMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = variableChecked ∨ symbol = variableEnd ∨
    ∃ bit : Bool, symbol = ofBool bit

@[simp] theorem variableToSeparatorMarker_checked :
    variableToSeparatorMarker variableChecked := Or.inl rfl
@[simp] theorem variableToSeparatorMarker_end :
    variableToSeparatorMarker variableEnd := Or.inr (Or.inl rfl)
@[simp] theorem variableToSeparatorMarker_ofBool (bit : Bool) :
    variableToSeparatorMarker (ofBool bit) := Or.inr (Or.inr ⟨bit, rfl⟩)

@[simp] theorem step_variableToSeparator_marker
    (marker : SATMachineSymbol)
    (hmarker : variableToSeparatorMarker marker)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableToSeparator blank left (marker :: right)) =
    configAt variableToSeparator blank (marker :: left) right := by
  rcases hmarker with rfl | rfl | ⟨bit, rfl⟩
  · rfl
  · rfl
  · cases bit <;> rfl

@[simp] theorem step_variableToSeparator_separator
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableToSeparator blank left (separator :: right)) =
    configAt variableFindAssignmentCount blank (separator :: left) right := by
  rfl

@[simp] theorem step_variableFindAssignment_checked
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableFindAssignmentCount blank left
        (assignmentLengthChecked :: right)) =
    configAt variableFindAssignmentCount blank
      (assignmentLengthChecked :: left) right := by
  rfl

@[simp] theorem step_variableFindAssignment_count
    (leftHead : SATMachineSymbol)
    (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableFindAssignmentCount blank
        (leftHead :: leftTail) (assignmentLengthCount :: right)) =
    configAt variableReturn blank leftTail
      (leftHead :: assignmentLengthChecked :: right) := by
  rfl

/-- Symbols crossed on the left-moving return from one consumed assignment
count marker to the variable-end marker. -/
def variableReturnMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = assignmentLengthChecked ∨ symbol = separator ∨
    ∃ bit : Bool, symbol = ofBool bit

@[simp] theorem variableReturnMarker_checked :
    variableReturnMarker assignmentLengthChecked := Or.inl rfl
@[simp] theorem variableReturnMarker_separator :
    variableReturnMarker separator := Or.inr (Or.inl rfl)
@[simp] theorem variableReturnMarker_ofBool (bit : Bool) :
    variableReturnMarker (ofBool bit) := Or.inr (Or.inr ⟨bit, rfl⟩)

@[simp] theorem step_variableReturn_marker
    (marker : SATMachineSymbol)
    (hmarker : variableReturnMarker marker)
    (leftHead : SATMachineSymbol)
    (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableReturn blank (leftHead :: leftTail) (marker :: right)) =
    configAt variableReturn blank leftTail (leftHead :: marker :: right) := by
  rcases hmarker with rfl | rfl | ⟨bit, rfl⟩
  · rfl
  · rfl
  · cases bit <;> rfl

@[simp] theorem step_variableReturn_end
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableReturn blank left (variableEnd :: right)) =
    match left with
    | [] => configAt variableFindLive blank [] (blank :: variableEnd :: right)
    | head :: tail => configAt variableFindLive blank tail (head :: variableEnd :: right) := by
  cases left <;> rfl

/-- One variable-selection loop, before the final scan over already checked
variable markers. `remaining` counts live markers strictly to the left of the
current live marker. -/
def variableLoopConfig
    (done remaining : Nat)
    (tail assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt variableFindLive blank
    (List.replicate remaining variableLive ++ [blank])
    (variableLive :: List.replicate done variableChecked ++
      variableEnd :: tail.map ofBool ++ separator ::
        List.replicate done assignmentLengthChecked ++
          List.replicate (remaining + 1) assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++
              suffix.map ofBool)

end SATMachineCertificatePhase
end OpenProblems.Complexity

namespace OpenProblems.Complexity
open OpenProblems
open OpenProblems.Universal
namespace SATMachineCertificatePhase
open SATMachineSymbol SATMachineState

/-- Marker block crossed on the right in one variable/count pairing cycle. -/
def variableToSeparatorMarkers (done : Nat) (tail : BitString) : List SATMachineSymbol :=
  List.replicate done variableChecked ++ variableEnd :: tail.map ofBool

@[simp] theorem variableToSeparatorMarkers_length (done : Nat) (tail : BitString) :
    (variableToSeparatorMarkers done tail).length = done + 1 + tail.length := by
  simp [variableToSeparatorMarkers]
  omega

theorem variableToSeparatorMarkers_all
    (done : Nat) (tail : BitString) (marker : SATMachineSymbol)
    (hmem : marker ∈ variableToSeparatorMarkers done tail) :
    variableToSeparatorMarker marker := by
  unfold variableToSeparatorMarkers at hmem
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hmem
  rcases hmem with hchecked | hend | htail
  · rcases hchecked with ⟨_, rfl⟩
    exact variableToSeparatorMarker_checked
  · subst marker
    exact variableToSeparatorMarker_end
  · rcases List.mem_map.mp htail with ⟨bit, _, rfl⟩
    exact variableToSeparatorMarker_ofBool bit

/-- Marker block crossed on the left when returning from the consumed
assignment-count marker. -/
def variableReturnMarkers (done : Nat) (tail : BitString) : List SATMachineSymbol :=
  List.replicate done assignmentLengthChecked ++
    separator :: (tail.map ofBool).reverse

@[simp] theorem variableReturnMarkers_length (done : Nat) (tail : BitString) :
    (variableReturnMarkers done tail).length = done + 1 + tail.length := by
  simp [variableReturnMarkers]
  omega

@[simp] theorem variableReturnMarkers_reverse (done : Nat) (tail : BitString) :
    (variableReturnMarkers done tail).reverse =
      tail.map ofBool ++ separator :: List.replicate done assignmentLengthChecked := by
  simp [variableReturnMarkers, List.reverse_append, List.append_assoc]

theorem variableReturnMarkers_all
    (done : Nat) (tail : BitString) (marker : SATMachineSymbol)
    (hmem : marker ∈ variableReturnMarkers done tail) :
    variableReturnMarker marker := by
  unfold variableReturnMarkers at hmem
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hmem
  rcases hmem with hchecked | hsep | htail
  · rcases hchecked with ⟨_, rfl⟩
    exact variableReturnMarker_checked
  · subst marker
    exact variableReturnMarker_separator
  · have htail' : marker ∈ tail.map ofBool := by
      simpa using List.mem_reverse.mp htail
    rcases List.mem_map.mp htail' with ⟨bit, _, rfl⟩
    exact variableReturnMarker_ofBool bit

/-- State immediately after one variable marker has consumed one assignment
length-count marker and returned to the variable block. -/
def variablePostReturnConfig
    (done remaining : Nat)
    (tail assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt variableFindLive blank
    (List.replicate done variableChecked ++
      List.replicate remaining variableLive ++ [blank])
    (variableChecked :: variableEnd :: tail.map ofBool ++ separator ::
      List.replicate (done + 1) assignmentLengthChecked ++
        List.replicate remaining assignmentLengthCount ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++
            suffix.map ofBool)

/-- Exact core cost of one variable/count pairing, ending before the checked
variable markers are scanned leftward. -/
theorem run_variable_pair_core
    (done remaining : Nat)
    (tail assignment suffix : BitString) :
    satControl.run (3 * done + 2 * tail.length + 6)
      (variableLoopConfig done remaining tail assignment suffix) =
    variablePostReturnConfig done remaining tail assignment suffix := by
  let toSep := variableToSeparatorMarkers done tail
  let ret := variableReturnMarkers done tail
  have htoSep : ∀ marker ∈ toSep, variableToSeparatorMarker marker := by
    intro marker hmem
    exact variableToSeparatorMarkers_all done tail marker hmem
  have hret : ∀ marker ∈ ret, variableReturnMarker marker := by
    intro marker hmem
    exact variableReturnMarkers_all done tail marker hmem
  have hstart :
      satControl.run 1
        (variableLoopConfig done remaining tail assignment suffix) =
      configAt variableToSeparator blank
        (variableChecked :: List.replicate remaining variableLive ++ [blank])
        (toSep ++ separator ::
          List.replicate done assignmentLengthChecked ++
            List.replicate (remaining + 1) assignmentLengthCount ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    unfold variableLoopConfig toSep variableToSeparatorMarkers
    rfl
  have hscan := run_keepRight_markers variableToSeparator
    variableToSeparatorMarker toSep
    (variableChecked :: List.replicate remaining variableLive ++ [blank])
    (separator :: List.replicate done assignmentLengthChecked ++
      List.replicate (remaining + 1) assignmentLengthCount ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    step_variableToSeparator_marker htoSep
  have hsep :
      satControl.run 1
        (configAt variableToSeparator blank
          (toSep.reverse ++ variableChecked ::
            List.replicate remaining variableLive ++ [blank])
          (separator :: List.replicate done assignmentLengthChecked ++
            List.replicate (remaining + 1) assignmentLengthCount ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt variableFindAssignmentCount blank
        (separator :: toSep.reverse ++ variableChecked ::
          List.replicate remaining variableLive ++ [blank])
        (List.replicate done assignmentLengthChecked ++
          List.replicate (remaining + 1) assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    exact step_variableToSeparator_separator
      (toSep.reverse ++ variableChecked ::
        List.replicate remaining variableLive ++ [blank])
      (List.replicate done assignmentLengthChecked ++
        List.replicate (remaining + 1) assignmentLengthCount ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
  have hcounts := run_keepRight_markers variableFindAssignmentCount
    (fun marker => marker = assignmentLengthChecked)
    (List.replicate done assignmentLengthChecked)
    (separator :: toSep.reverse ++ variableChecked ::
      List.replicate remaining variableLive ++ [blank])
    (List.replicate (remaining + 1) assignmentLengthCount ++
      assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    (by
      intro marker hm l r
      subst marker
      exact step_variableFindAssignment_checked l r)
    (by simp)
  have hcountStep :
      satControl.run 1
        (configAt variableFindAssignmentCount blank
          (List.replicate done assignmentLengthChecked ++
            separator :: toSep.reverse ++ variableChecked ::
              List.replicate remaining variableLive ++ [blank])
          (List.replicate (remaining + 1) assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      keepLeftScanConfig variableReturn ret variableEnd
        (List.replicate (done + 1) variableChecked ++
          List.replicate remaining variableLive ++ [blank])
        (assignmentLengthChecked ::
          List.replicate remaining assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    unfold ret variableReturnMarkers toSep variableToSeparatorMarkers
    cases done with
    | zero =>
        simp
        rfl
    | succ d =>
        simp only [List.replicate_succ, List.cons_append]
        simp [keepLeftScanConfig, List.reverse_append, List.append_assoc,
          replicate_append_same_marker]
        rw [show d + 1 + 1 = Nat.succ (Nat.succ d) by omega]
        rfl
  have hreturn := run_keepLeft_markers variableReturn variableReturnMarker ret variableEnd
    (List.replicate (done + 1) variableChecked ++
      List.replicate remaining variableLive ++ [blank])
    (assignmentLengthChecked ::
      List.replicate remaining assignmentLengthCount ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    step_variableReturn_marker hret
  have hend :
      satControl.run 1
        (configAt variableReturn blank
          (List.replicate (done + 1) variableChecked ++
            List.replicate remaining variableLive ++ [blank])
          (variableEnd :: ret.reverse ++ assignmentLengthChecked ::
            List.replicate remaining assignmentLengthCount ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      variablePostReturnConfig done remaining tail assignment suffix := by
    rw [controlMachine_run_one]
    unfold variablePostReturnConfig ret
    rw [variableReturnMarkers_reverse]
    simp only [List.cons_append]
    rw [step_variableReturn_end]
    simp [List.replicate_succ, List.append_assoc, replicate_append_same_marker]
  have hp2 :
      satControl.run (1 + toSep.length)
        (variableLoopConfig done remaining tail assignment suffix) =
      configAt variableToSeparator blank
        (toSep.reverse ++ variableChecked :: List.replicate remaining variableLive ++ [blank])
        (separator :: List.replicate done assignmentLengthChecked ++
          List.replicate (remaining + 1) assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hstart]
    simpa [List.append_assoc] using hscan
  have hp3 :
      satControl.run (1 + toSep.length + 1)
        (variableLoopConfig done remaining tail assignment suffix) =
      configAt variableFindAssignmentCount blank
        (separator :: toSep.reverse ++ variableChecked :: List.replicate remaining variableLive ++ [blank])
        (List.replicate done assignmentLengthChecked ++
          List.replicate (remaining + 1) assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp2]
    exact hsep
  have hcounts' :
      satControl.run done
        (configAt variableFindAssignmentCount blank
          (separator :: toSep.reverse ++ variableChecked :: List.replicate remaining variableLive ++ [blank])
          (List.replicate done assignmentLengthChecked ++
            List.replicate (remaining + 1) assignmentLengthCount ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt variableFindAssignmentCount blank
        (List.replicate done assignmentLengthChecked ++
          separator :: toSep.reverse ++ variableChecked :: List.replicate remaining variableLive ++ [blank])
        (List.replicate (remaining + 1) assignmentLengthCount ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    simpa using hcounts
  have hp4 :
      satControl.run (1 + toSep.length + 1 + done)
        (variableLoopConfig done remaining tail assignment suffix) =
      configAt variableFindAssignmentCount blank
        (List.replicate done assignmentLengthChecked ++
          separator :: toSep.reverse ++ variableChecked :: List.replicate remaining variableLive ++ [blank])
        (List.replicate (remaining + 1) assignmentLengthCount ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp3]
    exact hcounts'
  have hp5 :
      satControl.run (1 + toSep.length + 1 + done + 1)
        (variableLoopConfig done remaining tail assignment suffix) =
      keepLeftScanConfig variableReturn ret variableEnd
        (List.replicate (done + 1) variableChecked ++
          List.replicate remaining variableLive ++ [blank])
        (assignmentLengthChecked :: List.replicate remaining assignmentLengthCount ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp4]
    exact hcountStep
  have hp6 :
      satControl.run (1 + toSep.length + 1 + done + 1 + ret.length)
        (variableLoopConfig done remaining tail assignment suffix) =
      configAt variableReturn blank
        (List.replicate (done + 1) variableChecked ++
          List.replicate remaining variableLive ++ [blank])
        (variableEnd :: ret.reverse ++ assignmentLengthChecked ::
          List.replicate remaining assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp5]
    simpa [List.append_assoc] using hreturn
  have hp7 :
      satControl.run (1 + toSep.length + 1 + done + 1 + ret.length + 1)
        (variableLoopConfig done remaining tail assignment suffix) =
      variablePostReturnConfig done remaining tail assignment suffix := by
    rw [controlMachine_run_add, hp6]
    exact hend
  have hcost :
      3 * done + 2 * tail.length + 6 =
        1 + toSep.length + 1 + done + 1 + ret.length + 1 := by
    simp [toSep, ret]
    omega
  rw [hcost]
  exact hp7

end SATMachineCertificatePhase
end OpenProblems.Complexity

namespace OpenProblems.Complexity
open OpenProblems
open OpenProblems.Universal
namespace SATMachineCertificatePhase
open SATMachineSymbol SATMachineState

@[simp] theorem step_variableFindLive_checked
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableFindLive blank (leftHead :: leftTail)
        (variableChecked :: right)) =
    configAt variableFindLive blank leftTail
      (leftHead :: variableChecked :: right) := by
  rfl

@[simp] theorem step_variableFindLive_blank
    (right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableFindLive blank [] (blank :: right)) =
    configAt variableFinishCheck blank [blank] right := by
  cases right <;> rfl

/-- Canonical state after all variable markers have been paired with all
assignment-length count markers, just before the final equality check. -/
def variableFinishConfig
    (count : Nat) (tail assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt variableFinishCheck blank [blank]
    (List.replicate count variableChecked ++ variableEnd ::
      tail.map ofBool ++ separator ::
        List.replicate count assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

/-- If at least one live variable remains to the left, scan the checked
variable block and expose the next live variable. -/
theorem run_postReturn_to_nextLoop
    (done remaining : Nat)
    (tail assignment suffix : BitString) :
    satControl.run (done + 1)
      (variablePostReturnConfig done (remaining + 1) tail assignment suffix) =
    variableLoopConfig (done + 1) remaining tail assignment suffix := by
  let markers := List.replicate (done + 1) variableChecked
  have hmarkers : ∀ marker ∈ markers, marker = variableChecked := by
    simp [markers]
  have hscan := run_keepLeft_markers variableFindLive
    (fun marker => marker = variableChecked)
    markers variableLive
    (List.replicate remaining variableLive ++ [blank])
    (variableEnd :: tail.map ofBool ++ separator ::
      List.replicate (done + 1) assignmentLengthChecked ++
        List.replicate (remaining + 1) assignmentLengthCount ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_variableFindLive_checked leftHead leftTail right)
    hmarkers
  simpa [variablePostReturnConfig, variableLoopConfig, markers,
    keepLeftScanConfig, List.replicate_succ, List.append_assoc,
    replicate_append_same_marker] using hscan

/-- If no live variable remains, scan all checked variable markers to the blank
sentinel and enter the final count-equality check. -/
theorem run_postReturn_to_finish
    (done : Nat) (tail assignment suffix : BitString) :
    satControl.run (done + 2)
      (variablePostReturnConfig done 0 tail assignment suffix) =
    variableFinishConfig (done + 1) tail assignment suffix := by
  let markers := List.replicate (done + 1) variableChecked
  have hmarkers : ∀ marker ∈ markers, marker = variableChecked := by
    simp [markers]
  have hscan := run_keepLeft_markers variableFindLive
    (fun marker => marker = variableChecked)
    markers blank []
    (variableEnd :: tail.map ofBool ++ separator ::
      List.replicate (done + 1) assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    (by
      intro marker hm leftHead leftTail right
      subst marker
      exact step_variableFindLive_checked leftHead leftTail right)
    hmarkers
  have hscan' :
      satControl.run markers.length
        (variablePostReturnConfig done 0 tail assignment suffix) =
      configAt variableFindLive blank []
        (blank :: markers.reverse ++ variableEnd :: tail.map ofBool ++ separator ::
          List.replicate (done + 1) assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    have hnonempty : done + 1 = Nat.succ done := by omega
    rw [hnonempty] at hscan
    simpa [variablePostReturnConfig, markers, keepLeftScanConfig,
      List.replicate_succ, List.append_assoc, replicate_append_same_marker] using hscan
  have hblank :
      satControl.run 1
        (configAt variableFindLive blank []
          (blank :: markers.reverse ++ variableEnd :: tail.map ofBool ++ separator ::
            List.replicate (done + 1) assignmentLengthChecked ++
              assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      variableFinishConfig (done + 1) tail assignment suffix := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_variableFindLive_blank]
    unfold variableFinishConfig markers
    simp
  rw [show done + 2 = markers.length + 1 by simp [markers]]
  rw [controlMachine_run_add, hscan']
  exact hblank

/-- Closed cost from a live-variable loop entry through the final
`variableFinishCheck` state. `remaining + 1` is the number of variables still
unpaired, including the current head marker. -/
def variableLoopCost (done remaining tailLength : Nat) : Nat :=
  2 * (remaining + 1) * (remaining + 1) +
    (4 * done + 2 * tailLength + 5) * (remaining + 1) + 1

@[simp] theorem variableLoopCost_zero
    (done tailLength : Nat) :
    variableLoopCost done 0 tailLength = 4 * done + 2 * tailLength + 8 := by
  unfold variableLoopCost
  omega

/-- Cost recurrence matching one completed variable/count pairing followed by
its checked-marker left scan. -/
theorem variableLoopCost_succ
    (done remaining tailLength : Nat) :
    variableLoopCost done (remaining + 1) tailLength =
      (3 * done + 2 * tailLength + 6) + (done + 1) +
        variableLoopCost (done + 1) remaining tailLength := by
  unfold variableLoopCost
  simp only [Nat.add_mul, Nat.mul_succ, Nat.succ_mul]
  omega

/-- Complete variable/count pairing loop, from a current live variable through
entry into the final count-equality check. -/
theorem run_variable_loops
    (done remaining : Nat)
    (tail assignment suffix : BitString) :
    satControl.run (variableLoopCost done remaining tail.length)
      (variableLoopConfig done remaining tail assignment suffix) =
    variableFinishConfig (done + remaining + 1) tail assignment suffix := by
  induction remaining generalizing done with
  | zero =>
      have hcore := run_variable_pair_core done 0 tail assignment suffix
      have hfinish := run_postReturn_to_finish done tail assignment suffix
      have hprefix :
          satControl.run ((3 * done + 2 * tail.length + 6) + (done + 2))
            (variableLoopConfig done 0 tail assignment suffix) =
          variableFinishConfig (done + 1) tail assignment suffix := by
        rw [controlMachine_run_add, hcore]
        exact hfinish
      rw [variableLoopCost_zero]
      rw [show 4 * done + 2 * tail.length + 8 =
        (3 * done + 2 * tail.length + 6) + (done + 2) by omega]
      exact hprefix
  | succ remaining ih =>
      have hcore := run_variable_pair_core done (remaining + 1) tail assignment suffix
      have hnext := run_postReturn_to_nextLoop done remaining tail assignment suffix
      have hprefix :
          satControl.run ((3 * done + 2 * tail.length + 6) + (done + 1))
            (variableLoopConfig done (remaining + 1) tail assignment suffix) =
          variableLoopConfig (done + 1) remaining tail assignment suffix := by
        rw [controlMachine_run_add, hcore]
        exact hnext
      have hrec := ih (done := done + 1)
      rw [variableLoopCost_succ]
      rw [show (3 * done + 2 * tail.length + 6) + (done + 1) +
          variableLoopCost (done + 1) remaining tail.length =
        ((3 * done + 2 * tail.length + 6) + (done + 1)) +
          variableLoopCost (done + 1) remaining tail.length by omega]
      rw [controlMachine_run_add, hprefix, hrec]
      congr 2
      omega

end SATMachineCertificatePhase
end OpenProblems.Complexity

namespace OpenProblems.Complexity
open OpenProblems
open OpenProblems.Universal
namespace SATMachineCertificatePhase
open SATMachineSymbol SATMachineState

@[simp] theorem step_variableLength_true
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableLength blank left (ofBool true :: right)) =
    configAt variableLength blank (variableLive :: left) right := by
  rfl

/-- Exact scan of a unary variable-count prefix. -/
theorem run_variableLength_trues
    (n : Nat) (left payload : List SATMachineSymbol) :
    satControl.run n
      (configAt variableLength blank left
        (List.replicate n (ofBool true) ++ payload)) =
    configAt variableLength blank
      (List.replicate n variableLive ++ left) payload := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 = 1 + n by omega]
      rw [controlMachine_run_add, controlMachine_run_one]
      simp only [List.cons_append]
      rw [step_variableLength_true]
      simpa [List.replicate_succ, List.append_assoc, Nat.add_comm,
        replicate_append_same_marker] using
        (ih (left := variableLive :: left))

@[simp] theorem step_variableLength_false
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableLength blank (leftHead :: leftTail) (ofBool false :: right)) =
    configAt variableFindLive blank leftTail (leftHead :: variableEnd :: right) := by
  rfl

@[simp] theorem step_variableLength_false_to_loop
    (n : Nat) (tail assignment suffix : BitString) :
    satControl.stepConfig
      (configAt variableLength blank
        (List.replicate n variableLive ++ variableLive :: [blank])
        (ofBool false :: tail.map ofBool ++ separator ::
          List.replicate (n + 1) assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
    variableLoopConfig 0 n tail assignment suffix := by
  rw [replicate_append_same_marker n variableLive [blank]]
  rw [List.replicate_succ]
  simp only [List.cons_append]
  rw [step_variableLength_false]
  unfold variableLoopConfig
  simp [List.append_assoc, List.replicate_succ]

@[simp] theorem step_variableLength_false_zero
    (tail assignment suffix : BitString) :
    satControl.stepConfig
      (configAt variableLength blank [blank]
        (ofBool false :: tail.map ofBool ++ separator ::
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
    configAt variableFindLive blank []
      (blank :: variableEnd :: tail.map ofBool ++ separator ::
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
  rfl

/-- For a positive unary variable count, the initial scan reaches the first
variable/count pairing loop exactly. -/
theorem run_variableLength_prefix_to_loop
    (n : Nat) (tail assignment suffix : BitString)
    (hlen : assignment.length = n + 1) :
    satControl.run (n + 2)
      (variableLengthEntryConfig
        (List.replicate (n + 1) true ++ false :: tail)
        assignment suffix) =
    variableLoopConfig 0 n tail assignment suffix := by
  have hscan := run_variableLength_trues (n + 1) [blank]
    (ofBool false :: tail.map ofBool ++ separator ::
      List.replicate assignment.length assignmentLengthCount ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
  have hscan' :
      satControl.run (n + 1)
        (variableLengthEntryConfig
          (List.replicate (n + 1) true ++ false :: tail)
          assignment suffix) =
      configAt variableLength blank
        (List.replicate n variableLive ++ variableLive :: [blank])
        (ofBool false :: tail.map ofBool ++ separator ::
          List.replicate (n + 1) assignmentLengthCount ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    unfold variableLengthEntryConfig at hscan ⊢
    rw [hlen] at hscan ⊢
    simpa [List.map_append, List.replicate_succ, List.append_assoc,
      replicate_append_same_marker] using hscan
  rw [show n + 2 = (n + 1) + 1 by omega]
  rw [controlMachine_run_add, hscan', controlMachine_run_one]
  exact step_variableLength_false_to_loop n tail assignment suffix

/-- Entry into `variableFinishCheck` for the zero-variable case. -/
theorem run_variableLength_zero_to_finish
    (tail assignment suffix : BitString)
    (hlen : assignment.length = 0) :
    satControl.run 2
      (variableLengthEntryConfig (false :: tail) assignment suffix) =
    variableFinishConfig 0 tail assignment suffix := by
  have hfalse :
      satControl.run 1
        (variableLengthEntryConfig (false :: tail) assignment suffix) =
      configAt variableFindLive blank []
        (blank :: variableEnd :: tail.map ofBool ++ separator ::
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    simp [variableLengthEntryConfig, hlen, List.append_assoc]
  have hblank :
      satControl.run 1
        (configAt variableFindLive blank []
          (blank :: variableEnd :: tail.map ofBool ++ separator ::
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      variableFinishConfig 0 tail assignment suffix := by
    rw [controlMachine_run_one]
    simp only [List.cons_append]
    rw [step_variableFindLive_blank]
    simp [variableFinishConfig, List.append_assoc]
  rw [show 2 = 1 + 1 by omega]
  rw [controlMachine_run_add, hfalse]
  exact hblank

/-- Exact cost through all variable/count pairings and into the final equality
check. -/
def variablePrefixCost (count tailLength : Nat) : Nat :=
  2 * count * count + 6 * count + 2 * count * tailLength + 2

/-- Complete unary variable-count scan and exact pairing with the normalized
assignment-length markers. -/
theorem run_variableLength_to_finish
    (count : Nat) (tail assignment suffix : BitString)
    (hlen : assignment.length = count) :
    satControl.run (variablePrefixCost count tail.length)
      (variableLengthEntryConfig
        (List.replicate count true ++ false :: tail)
        assignment suffix) =
    variableFinishConfig count tail assignment suffix := by
  cases count with
  | zero =>
      simp only [variablePrefixCost, Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
      simpa using run_variableLength_zero_to_finish tail assignment suffix hlen
  | succ n =>
      have hprefix := run_variableLength_prefix_to_loop n tail assignment suffix (by omega)
      have hloops := run_variable_loops 0 n tail assignment suffix
      have hcombo :
          satControl.run ((n + 2) + variableLoopCost 0 n tail.length)
            (variableLengthEntryConfig
              (List.replicate (n + 1) true ++ false :: tail)
              assignment suffix) =
          variableFinishConfig (n + 1) tail assignment suffix := by
        rw [controlMachine_run_add, hprefix]
        simpa using hloops
      have hcost :
          variablePrefixCost (n + 1) tail.length =
            (n + 2) + variableLoopCost 0 n tail.length := by
        unfold variablePrefixCost variableLoopCost
        simp only [Nat.add_mul, Nat.mul_succ, Nat.succ_mul]
        rw [Nat.mul_comm tail.length n]
        omega
      rw [hcost]
      exact hcombo

/-- Symbols crossed while the final variable block is checked against the
certificate separator. -/
def variableFinishMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = variableChecked ∨ symbol = variableEnd ∨
    ∃ bit : Bool, symbol = ofBool bit

@[simp] theorem variableFinishMarker_checked : variableFinishMarker variableChecked := Or.inl rfl
@[simp] theorem variableFinishMarker_end : variableFinishMarker variableEnd := Or.inr (Or.inl rfl)
@[simp] theorem variableFinishMarker_ofBool (bit : Bool) : variableFinishMarker (ofBool bit) :=
  Or.inr (Or.inr ⟨bit, rfl⟩)

@[simp] theorem step_variableFinish_marker
    (marker : SATMachineSymbol) (hmarker : variableFinishMarker marker)
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableFinishCheck blank left (marker :: right)) =
    configAt variableFinishCheck blank (marker :: left) right := by
  rcases hmarker with rfl | rfl | ⟨bit, rfl⟩
  · rfl
  · rfl
  · cases bit <;> rfl

@[simp] theorem step_variableFinish_separator
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableFinishCheck blank left (separator :: right)) =
    configAt variableCheckAssignment blank (separator :: left) right := by
  rfl

@[simp] theorem step_variableCheck_checked
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableCheckAssignment blank left
        (assignmentLengthChecked :: right)) =
    configAt variableCheckAssignment blank
      (assignmentLengthChecked :: left) right := by
  rfl

@[simp] theorem step_variableCheck_end
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableCheckAssignment blank (leftHead :: leftTail)
        (assignmentLengthEnd :: right)) =
    configAt variableToFormula blank leftTail
      (leftHead :: assignmentLengthEnd :: right) := by
  rfl

/-- Symbols crossed leftward after the exact assignment-length equality check. -/
def variableToFormulaMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = assignmentLengthChecked ∨ symbol = separator ∨
    ∃ bit : Bool, symbol = ofBool bit

@[simp] theorem variableToFormulaMarker_checked :
    variableToFormulaMarker assignmentLengthChecked := Or.inl rfl
@[simp] theorem variableToFormulaMarker_separator :
    variableToFormulaMarker separator := Or.inr (Or.inl rfl)
@[simp] theorem variableToFormulaMarker_ofBool (bit : Bool) :
    variableToFormulaMarker (ofBool bit) := Or.inr (Or.inr ⟨bit, rfl⟩)

@[simp] theorem step_variableToFormula_marker
    (marker : SATMachineSymbol) (hmarker : variableToFormulaMarker marker)
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableToFormula blank (leftHead :: leftTail) (marker :: right)) =
    configAt variableToFormula blank leftTail (leftHead :: marker :: right) := by
  rcases hmarker with rfl | rfl | ⟨bit, rfl⟩
  · rfl
  · rfl
  · cases bit <;> rfl

@[simp] theorem step_variableToFormula_end
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt variableToFormula blank left (variableEnd :: right)) =
    configAt formulaLength blank (variableEnd :: left) right := by
  rfl

/-- Canonical entry to the formula-length scan after exact variable-count
comparison succeeds. -/
def formulaLengthEntryConfig
    (count : Nat) (tail assignment suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  configAt formulaLength blank
    (variableEnd :: List.replicate count variableChecked ++ [blank])
    (tail.map ofBool ++ separator ::
      List.replicate count assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)

end SATMachineCertificatePhase
end OpenProblems.Complexity

namespace OpenProblems.Complexity
open OpenProblems
open OpenProblems.Universal
namespace SATMachineCertificatePhase
open SATMachineSymbol SATMachineState

/-- Right-moving marker block checked before crossing the certificate separator. -/
def variableFinishMarkers (count : Nat) (tail : BitString) : List SATMachineSymbol :=
  List.replicate count variableChecked ++ variableEnd :: tail.map ofBool

@[simp] theorem variableFinishMarkers_length (count : Nat) (tail : BitString) :
    (variableFinishMarkers count tail).length = count + 1 + tail.length := by
  simp [variableFinishMarkers]
  omega

theorem variableFinishMarkers_all
    (count : Nat) (tail : BitString) (marker : SATMachineSymbol)
    (hmem : marker ∈ variableFinishMarkers count tail) :
    variableFinishMarker marker := by
  unfold variableFinishMarkers at hmem
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hmem
  rcases hmem with hchecked | hend | htail
  · rcases hchecked with ⟨_, rfl⟩
    exact variableFinishMarker_checked
  · subst marker
    exact variableFinishMarker_end
  · rcases List.mem_map.mp htail with ⟨bit, _, rfl⟩
    exact variableFinishMarker_ofBool bit

/-- Left-moving marker block crossed after the assignment-length end marker. -/
def variableToFormulaMarkers (count : Nat) (tail : BitString) : List SATMachineSymbol :=
  List.replicate count assignmentLengthChecked ++
    separator :: (tail.map ofBool).reverse

@[simp] theorem variableToFormulaMarkers_length (count : Nat) (tail : BitString) :
    (variableToFormulaMarkers count tail).length = count + 1 + tail.length := by
  simp [variableToFormulaMarkers]
  omega

@[simp] theorem variableToFormulaMarkers_reverse (count : Nat) (tail : BitString) :
    (variableToFormulaMarkers count tail).reverse =
      tail.map ofBool ++ separator :: List.replicate count assignmentLengthChecked := by
  simp [variableToFormulaMarkers, List.reverse_append, List.append_assoc]

theorem variableToFormulaMarkers_all
    (count : Nat) (tail : BitString) (marker : SATMachineSymbol)
    (hmem : marker ∈ variableToFormulaMarkers count tail) :
    variableToFormulaMarker marker := by
  unfold variableToFormulaMarkers at hmem
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hmem
  rcases hmem with hchecked | hsep | htail
  · rcases hchecked with ⟨_, rfl⟩
    exact variableToFormulaMarker_checked
  · subst marker
    exact variableToFormulaMarker_separator
  · have htail' : marker ∈ tail.map ofBool := by
      simpa using List.mem_reverse.mp htail
    rcases List.mem_map.mp htail' with ⟨bit, _, rfl⟩
    exact variableToFormulaMarker_ofBool bit

/-- Exact successful variable-count equality check and return to the formula
length prefix. -/
theorem run_variableFinish_to_formulaLength
    (count : Nat) (tail assignment suffix : BitString) :
    satControl.run (3 * count + 2 * tail.length + 5)
      (variableFinishConfig count tail assignment suffix) =
    formulaLengthEntryConfig count tail assignment suffix := by
  let forward := variableFinishMarkers count tail
  let backward := variableToFormulaMarkers count tail
  have hforward : ∀ marker ∈ forward, variableFinishMarker marker := by
    intro marker hmem
    exact variableFinishMarkers_all count tail marker hmem
  have hbackward : ∀ marker ∈ backward, variableToFormulaMarker marker := by
    intro marker hmem
    exact variableToFormulaMarkers_all count tail marker hmem
  have hscanForward := run_keepRight_markers variableFinishCheck
    variableFinishMarker forward [blank]
    (separator :: List.replicate count assignmentLengthChecked ++
      assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    step_variableFinish_marker hforward
  have hsep :
      satControl.run 1
        (configAt variableFinishCheck blank
          (forward.reverse ++ [blank])
          (separator :: List.replicate count assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt variableCheckAssignment blank
        (separator :: forward.reverse ++ [blank])
        (List.replicate count assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    exact step_variableFinish_separator
      (forward.reverse ++ [blank])
      (List.replicate count assignmentLengthChecked ++
        assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
  have hscanCounts := run_keepRight_markers variableCheckAssignment
    (fun marker => marker = assignmentLengthChecked)
    (List.replicate count assignmentLengthChecked)
    (separator :: forward.reverse ++ [blank])
    (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    (by
      intro marker hm left right
      subst marker
      exact step_variableCheck_checked left right)
    (by simp)
  have hend :
      satControl.run 1
        (configAt variableCheckAssignment blank
          (List.replicate count assignmentLengthChecked ++
            separator :: forward.reverse ++ [blank])
          (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      keepLeftScanConfig variableToFormula backward variableEnd
        (List.replicate count variableChecked ++ [blank])
        (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_one]
    unfold forward variableFinishMarkers backward variableToFormulaMarkers
    cases count with
    | zero =>
        simp [keepLeftScanConfig, List.append_assoc]
    | succ n =>
        simp only [List.replicate_succ, List.cons_append]
        simp [keepLeftScanConfig, List.reverse_append, List.append_assoc,
          replicate_append_same_marker]
        rw [show n + 1 = Nat.succ n by omega]
        rfl
  have hscanBackward := run_keepLeft_markers variableToFormula
    variableToFormulaMarker backward variableEnd
    (List.replicate count variableChecked ++ [blank])
    (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)
    step_variableToFormula_marker hbackward
  have hfinal :
      satControl.run 1
        (configAt variableToFormula blank
          (List.replicate count variableChecked ++ [blank])
          (variableEnd :: backward.reverse ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      formulaLengthEntryConfig count tail assignment suffix := by
    rw [controlMachine_run_one]
    unfold backward
    rw [variableToFormulaMarkers_reverse]
    simp only [List.cons_append]
    rw [step_variableToFormula_end]
    unfold formulaLengthEntryConfig
    simp [List.append_assoc]
  have hp1 :
      satControl.run forward.length
        (variableFinishConfig count tail assignment suffix) =
      configAt variableFinishCheck blank
        (forward.reverse ++ [blank])
        (separator :: List.replicate count assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    unfold variableFinishConfig forward variableFinishMarkers at hscanForward ⊢
    simpa [List.append_assoc] using hscanForward
  have hp2 :
      satControl.run (forward.length + 1)
        (variableFinishConfig count tail assignment suffix) =
      configAt variableCheckAssignment blank
        (separator :: forward.reverse ++ [blank])
        (List.replicate count assignmentLengthChecked ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp1]
    exact hsep
  have hscanCounts' :
      satControl.run count
        (configAt variableCheckAssignment blank
          (separator :: forward.reverse ++ [blank])
          (List.replicate count assignmentLengthChecked ++
            assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool)) =
      configAt variableCheckAssignment blank
        (List.replicate count assignmentLengthChecked ++
          separator :: forward.reverse ++ [blank])
        (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    simpa using hscanCounts
  have hp3 :
      satControl.run (forward.length + 1 + count)
        (variableFinishConfig count tail assignment suffix) =
      configAt variableCheckAssignment blank
        (List.replicate count assignmentLengthChecked ++
          separator :: forward.reverse ++ [blank])
        (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp2]
    exact hscanCounts'
  have hp4 :
      satControl.run (forward.length + 1 + count + 1)
        (variableFinishConfig count tail assignment suffix) =
      keepLeftScanConfig variableToFormula backward variableEnd
        (List.replicate count variableChecked ++ [blank])
        (assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp3]
    exact hend
  have hp5 :
      satControl.run (forward.length + 1 + count + 1 + backward.length)
        (variableFinishConfig count tail assignment suffix) =
      configAt variableToFormula blank
        (List.replicate count variableChecked ++ [blank])
        (variableEnd :: backward.reverse ++
          assignmentLengthEnd :: assignment.map assignmentSymbol ++ suffix.map ofBool) := by
    rw [controlMachine_run_add, hp4]
    simpa [List.append_assoc] using hscanBackward
  have hp6 :
      satControl.run (forward.length + 1 + count + 1 + backward.length + 1)
        (variableFinishConfig count tail assignment suffix) =
      formulaLengthEntryConfig count tail assignment suffix := by
    rw [controlMachine_run_add, hp5]
    exact hfinal
  have hcost :
      3 * count + 2 * tail.length + 5 =
        forward.length + 1 + count + 1 + backward.length + 1 := by
    simp [forward, backward]
    omega
  rw [hcost]
  exact hp6

/-- Full variable-count phase: unary instance variable count, one-to-one
comparison with the normalized assignment length, exact exhaustion check, and
entry into formula processing. -/
def variablePhaseCost (count tailLength : Nat) : Nat :=
  2 * count * count + 9 * count + 2 * (count + 1) * tailLength + 7

theorem run_variablePhase
    (count : Nat) (tail assignment suffix : BitString)
    (hlen : assignment.length = count) :
    satControl.run (variablePhaseCost count tail.length)
      (variableLengthEntryConfig
        (List.replicate count true ++ false :: tail)
        assignment suffix) =
    formulaLengthEntryConfig count tail assignment suffix := by
  have hp := run_variableLength_to_finish count tail assignment suffix hlen
  have hf := run_variableFinish_to_formulaLength count tail assignment suffix
  have hcombo :
      satControl.run
        (variablePrefixCost count tail.length +
          (3 * count + 2 * tail.length + 5))
        (variableLengthEntryConfig
          (List.replicate count true ++ false :: tail)
          assignment suffix) =
      formulaLengthEntryConfig count tail assignment suffix := by
    rw [controlMachine_run_add, hp]
    exact hf
  have hcost :
      variablePhaseCost count tail.length =
        variablePrefixCost count tail.length +
          (3 * count + 2 * tail.length + 5) := by
    unfold variablePhaseCost variablePrefixCost
    rw [Nat.mul_add]
    simp only [Nat.mul_one]
    rw [Nat.add_mul]
    omega
  rw [hcost]
  exact hcombo

end SATMachineCertificatePhase
end OpenProblems.Complexity

namespace OpenProblems.Complexity
open OpenProblems
open OpenProblems.Universal
namespace SATMachineCertificatePhase
open SATMachineSymbol SATMachineState

/-- The encoded formula tail that follows the unary instance variable count. -/
def encodedInstanceFormulaTail (inst : CNF.Instance) : BitString :=
  List.replicate inst.formula.length true ++
    false :: CNF.clauseCodec.encodeListPayload inst.formula

@[simp] theorem encodedInstance_eq_variablePrefix_tail (inst : CNF.Instance) :
    CNF.encodeInstance inst =
      List.replicate inst.variableCount true ++
        false :: encodedInstanceFormulaTail inst := by
  rw [CNF.encodeInstance_physical_layout]
  rfl

/-- For an assignment of exactly the declared variable count, the fixed SAT
machine completes the entire variable-count comparison and reaches the formula
length prefix of the same encoded instance. -/
theorem run_encodedInstance_variablePhase
    (inst : CNF.Instance) (assignment suffix : BitString)
    (hlen : assignment.length = inst.variableCount) :
    satControl.run
      (variablePhaseCost inst.variableCount
        (encodedInstanceFormulaTail inst).length)
      (variableLengthEntryConfig
        (CNF.encodeInstance inst) assignment suffix) =
    formulaLengthEntryConfig inst.variableCount
      (encodedInstanceFormulaTail inst) assignment suffix := by
  rw [encodedInstance_eq_variablePrefix_tail]
  exact run_variablePhase inst.variableCount
    (encodedInstanceFormulaTail inst) assignment suffix hlen

/-- Exact typed execution cost from the original verifier configuration through
certificate normalization and the complete variable-count phase. -/
def typedToFormulaLengthCost
    (inst : CNF.Instance) : Nat :=
  (2 * inst.variableCount * inst.variableCount +
    6 * inst.variableCount + 2 * (CNF.encodeInstance inst).length + 7) +
  variablePhaseCost inst.variableCount
    (encodedInstanceFormulaTail inst).length

/-- End-to-end typed prefix theorem: input scan, certificate normalization,
assignment pairing, variable-count equality, and entry to formula processing. -/
theorem run_typed_encodedInstance_to_formulaLength
    (inst : CNF.Instance) (assignment suffix : BitString)
    (hlen : assignment.length = inst.variableCount) :
    satControl.run (typedToFormulaLengthCost inst)
      (encodedSATTypedInitialConfig
        (CNF.encodeInstance inst)
        (CNF.encodeAssignment assignment ++ suffix)) =
    formulaLengthEntryConfig inst.variableCount
      (encodedInstanceFormulaTail inst) assignment suffix := by
  have hcert := run_typed_to_variableLength
    (CNF.encodeInstance inst) assignment suffix
  have hvar := run_encodedInstance_variablePhase inst assignment suffix hlen
  unfold typedToFormulaLengthCost
  rw [controlMachine_run_add]
  rw [show assignment.length = inst.variableCount by exact hlen] at hcert
  rw [hcert]
  exact hvar

/-- Raw finite-machine lowering preserves the complete prefix through formula
length entry. This is stated about the raw DTM used by `MachineVerifierRelation`. -/
theorem run_raw_encodedInstance_to_formulaLength
    (inst : CNF.Instance) (assignment suffix : BitString)
    (hlen : assignment.length = inst.variableCount) :
    encodedSATFiniteMachine.toDTM.run (typedToFormulaLengthCost inst)
      (FiniteControlMachine.encodeConfig
        (encodedSATTypedInitialConfig
          (CNF.encodeInstance inst)
          (CNF.encodeAssignment assignment ++ suffix))) =
    FiniteControlMachine.encodeConfig
      (formulaLengthEntryConfig inst.variableCount
        (encodedInstanceFormulaTail inst) assignment suffix) := by
  unfold encodedSATFiniteMachine
  calc
    _ = FiniteControlMachine.encodeConfig
        (satControl.run (typedToFormulaLengthCost inst)
          (encodedSATTypedInitialConfig
            (CNF.encodeInstance inst)
            (CNF.encodeAssignment assignment ++ suffix))) :=
      FiniteControlMachine.lowerAbsorbing_run_commutes
        encodedSATFiniteControl
        (typedToFormulaLengthCost inst)
        (encodedSATTypedInitialConfig
          (CNF.encodeInstance inst)
          (CNF.encodeAssignment assignment ++ suffix))
    _ = _ := congrArg FiniteControlMachine.encodeConfig
      (run_typed_encodedInstance_to_formulaLength inst assignment suffix hlen)

end SATMachineCertificatePhase
end OpenProblems.Complexity
