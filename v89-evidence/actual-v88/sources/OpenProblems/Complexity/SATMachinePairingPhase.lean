import OpenProblems.Complexity.SATMachineCertificatePhase

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState

@[simp] theorem step_toPayload_spent (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt certificateToPayload blank left (assignmentLengthSpent :: right)) =
    configAt certificateToPayload blank (assignmentLengthSpent :: left) right := by
  rfl

@[simp] theorem step_toPayload_end (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt certificateToPayload blank left (assignmentLengthEnd :: right)) =
    configAt certificateToPayload blank (assignmentLengthEnd :: left) right := by
  rfl

@[simp] theorem step_toPayload_assignment (left right : List SATMachineSymbol) (bit : Bool) :
    satControl.stepConfig
      (configAt certificateToPayload blank left (assignmentSymbol bit :: right)) =
    configAt certificateToPayload blank (assignmentSymbol bit :: left) right := by
  cases bit <;> rfl

@[simp] theorem step_toPayload_raw
    (leftHead : SATMachineSymbol) (leftTail right : List SATMachineSymbol) (bit : Bool) :
    satControl.stepConfig
      (configAt certificateToPayload blank (leftHead :: leftTail) (ofBool bit :: right)) =
    configAt certificateFindLive blank leftTail (leftHead :: assignmentSymbol bit :: right) := by
  cases bit <;> rfl

@[simp] theorem step_findLive_marker
    (leftHead marker : SATMachineSymbol) (leftTail right : List SATMachineSymbol)
    (hmarker : marker = assignmentLengthSpent ∨ marker = assignmentLengthEnd ∨
      marker = assignmentFalse ∨ marker = assignmentTrue) :
    satControl.stepConfig
      (configAt certificateFindLive blank (leftHead :: leftTail) (marker :: right)) =
    configAt certificateFindLive blank leftTail (leftHead :: marker :: right) := by
  rcases hmarker with rfl | rfl | rfl | rfl <;> rfl



def certificateMarker (symbol : SATMachineSymbol) : Prop :=
  symbol = assignmentLengthSpent ∨ symbol = assignmentLengthEnd ∨
    symbol = assignmentFalse ∨ symbol = assignmentTrue

@[simp] theorem certificateMarker_spent : certificateMarker assignmentLengthSpent := Or.inl rfl
@[simp] theorem certificateMarker_end : certificateMarker assignmentLengthEnd := Or.inr (Or.inl rfl)
@[simp] theorem certificateMarker_assignmentSymbol (bit : Bool) : certificateMarker (assignmentSymbol bit) := by
  cases bit <;> simp [certificateMarker, assignmentSymbol]


theorem replicate_append_same_marker
    (n : Nat) (a : SATMachineSymbol) (tail : List SATMachineSymbol) :
    List.replicate n a ++ a :: tail =
      List.replicate (n + 1) a ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact congrArg (fun xs => a :: xs) ih

theorem run_toPayload_replicate_spent
    (n : Nat) (left payload : List SATMachineSymbol) :
    satControl.run n
      (configAt certificateToPayload blank left
        (List.replicate n assignmentLengthSpent ++ payload)) =
    configAt certificateToPayload blank
      (List.replicate n assignmentLengthSpent ++ left) payload := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change satControl.run n
        (satControl.stepConfig
          (configAt certificateToPayload blank left
            (assignmentLengthSpent :: List.replicate n assignmentLengthSpent ++ payload))) = _
      have hstep :
          satControl.stepConfig
            (configAt certificateToPayload blank left
              ((assignmentLengthSpent :: List.replicate n assignmentLengthSpent) ++ payload)) =
          configAt certificateToPayload blank
            (assignmentLengthSpent :: left)
            (List.replicate n assignmentLengthSpent ++ payload) := by
        exact
          step_toPayload_spent left
            (List.replicate n assignmentLengthSpent ++ payload)
      rw [hstep]
      rw [ih]
      rw [replicate_append_same_marker n assignmentLengthSpent left]
      rw [List.replicate_succ]

theorem run_toPayload_assignmentSymbols
    (done : BitString) (left payload : List SATMachineSymbol) :
    satControl.run done.length
      (configAt certificateToPayload blank left
        (done.map assignmentSymbol ++ payload)) =
    configAt certificateToPayload blank
      ((done.map assignmentSymbol).reverse ++ left) payload := by
  induction done generalizing left with
  | nil => rfl
  | cons bit done ih =>
      simp only [List.map_cons, List.cons_append]
      change satControl.run (done.length + 1)
        (configAt certificateToPayload blank left
          (assignmentSymbol bit :: done.map assignmentSymbol ++ payload)) = _
      change satControl.run done.length
        (satControl.stepConfig
          (configAt certificateToPayload blank left
            (assignmentSymbol bit :: done.map assignmentSymbol ++ payload))) = _
      have hstep :
          satControl.stepConfig
            (configAt certificateToPayload blank left
              ((assignmentSymbol bit :: done.map assignmentSymbol) ++ payload)) =
          configAt certificateToPayload blank
            (assignmentSymbol bit :: left)
            (done.map assignmentSymbol ++ payload) := by
        exact
          step_toPayload_assignment left
            (done.map assignmentSymbol ++ payload) bit
      rw [hstep]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def leftScanConfig
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol) :
    Config SATMachineState SATMachineSymbol :=
  match markers with
  | [] => configAt certificateFindLive blank baseLeft (baseHead :: right)
  | marker :: remaining =>
      configAt certificateFindLive blank
        (remaining ++ baseHead :: baseLeft) (marker :: right)

theorem run_findLive_markers
    (markers : List SATMachineSymbol)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (hmarkers : ∀ marker ∈ markers, certificateMarker marker) :
    satControl.run markers.length
      (leftScanConfig markers baseHead baseLeft right) =
    configAt certificateFindLive blank baseLeft
      (baseHead :: markers.reverse ++ right) := by
  induction markers generalizing right with
  | nil => rfl
  | cons marker markers ih =>
      change satControl.run (markers.length + 1)
        (configAt certificateFindLive blank
          (markers ++ baseHead :: baseLeft) (marker :: right)) = _
      change satControl.run markers.length
        (satControl.stepConfig
          (configAt certificateFindLive blank
            (markers ++ baseHead :: baseLeft) (marker :: right))) = _
      have hm : certificateMarker marker := hmarkers marker (by simp)
      cases markers with
      | nil =>
          simp only [List.nil_append]
          rw [step_findLive_marker baseHead marker baseLeft right hm]
          rfl
      | cons next rest =>
          rw [List.cons_append]
          rw [step_findLive_marker next marker (rest ++ baseHead :: baseLeft) right hm]
          have htail : ∀ m ∈ (next :: rest), certificateMarker m := by
            intro m hmemb
            exact hmarkers m (by simp [hmemb])
          have hrec := ih (right := marker :: right) htail
          change satControl.run (List.length (next :: rest))
            (leftScanConfig (next :: rest) baseHead baseLeft (marker :: right)) = _ at hrec
          have hrec' :
              satControl.run (List.length (next :: rest))
                (configAt certificateFindLive blank
                  (rest ++ baseHead :: baseLeft) (next :: marker :: right)) =
                configAt certificateFindLive blank baseLeft
                  (baseHead :: (next :: rest).reverse ++ marker :: right) := by
            simpa [leftScanConfig] using hrec
          rw [hrec']
          simp [List.reverse_cons, List.append_assoc]



@[simp] theorem step_findLive_live
    (left right : List SATMachineSymbol) :
    satControl.stepConfig
      (configAt certificateFindLive blank left (assignmentLengthLive :: right)) =
    configAt certificateToPayload blank (assignmentLengthSpent :: left) right := by
  cases right <;> rfl

/-- Configuration with the next raw certificate bit under the head. -/
def pairingPayloadReadyConfig
    (inputLeft : List SATMachineSymbol)
    (done remaining suffix : BitString)
    (bit : Bool) :
    Config SATMachineState SATMachineSymbol :=
  configAt certificateToPayload blank
    ((done.map assignmentSymbol).reverse ++
      assignmentLengthEnd ::
        List.replicate (done.length + 1) assignmentLengthSpent ++
          List.replicate remaining.length assignmentLengthLive ++
            SATMachineSymbol.separator :: inputLeft)
    ((bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)

theorem run_pairing_to_payload_ready
    (inputLeft : List SATMachineSymbol)
    (done remaining suffix : BitString)
    (bit : Bool) :
    satControl.run (2 * done.length + 2)
      (pairingConfig inputLeft done (bit :: remaining) suffix) =
    pairingPayloadReadyConfig inputLeft done remaining suffix bit := by
  unfold pairingPayloadReadyConfig
  have hstart :
      satControl.stepConfig
        (configAt certificateFindLive blank
          (List.replicate remaining.length assignmentLengthLive ++
            SATMachineSymbol.separator :: inputLeft)
          (assignmentLengthLive ::
            List.replicate done.length assignmentLengthSpent ++
              assignmentLengthEnd :: done.map assignmentSymbol ++
                (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)) =
      configAt certificateToPayload blank
        (assignmentLengthSpent ::
          List.replicate remaining.length assignmentLengthLive ++
            SATMachineSymbol.separator :: inputLeft)
        (List.replicate done.length assignmentLengthSpent ++
          assignmentLengthEnd :: done.map assignmentSymbol ++
            (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool) := by
    exact
      step_findLive_live
        (List.replicate remaining.length assignmentLengthLive ++
          SATMachineSymbol.separator :: inputLeft)
        (List.replicate done.length assignmentLengthSpent ++
          assignmentLengthEnd :: done.map assignmentSymbol ++
            (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)
  have hspent := run_toPayload_replicate_spent done.length
    (assignmentLengthSpent ::
      List.replicate remaining.length assignmentLengthLive ++
        SATMachineSymbol.separator :: inputLeft)
    (assignmentLengthEnd :: done.map assignmentSymbol ++
      (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)
  have hend := step_toPayload_end
    (List.replicate done.length assignmentLengthSpent ++
      assignmentLengthSpent ::
        List.replicate remaining.length assignmentLengthLive ++
          SATMachineSymbol.separator :: inputLeft)
    (done.map assignmentSymbol ++
      (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)
  have htags := run_toPayload_assignmentSymbols done
    (assignmentLengthEnd ::
      List.replicate done.length assignmentLengthSpent ++
        assignmentLengthSpent ::
          List.replicate remaining.length assignmentLengthLive ++
            SATMachineSymbol.separator :: inputLeft)
    ((bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)
  have hstartRun :
      satControl.run 1 (pairingConfig inputLeft done (bit :: remaining) suffix) =
        configAt certificateToPayload blank
          (assignmentLengthSpent ::
            List.replicate remaining.length assignmentLengthLive ++
              SATMachineSymbol.separator :: inputLeft)
          (List.replicate done.length assignmentLengthSpent ++
            assignmentLengthEnd :: done.map assignmentSymbol ++
              (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool) := by
    rw [controlMachine_run_one]
    change satControl.stepConfig
      (configAt certificateFindLive blank
        (List.replicate remaining.length assignmentLengthLive ++
          SATMachineSymbol.separator :: inputLeft)
        (assignmentLengthLive ::
          List.replicate done.length assignmentLengthSpent ++
            assignmentLengthEnd :: done.map assignmentSymbol ++
              (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)) = _
    exact hstart
  have hprefix :
      satControl.run (1 + done.length)
        (pairingConfig inputLeft done (bit :: remaining) suffix) =
      configAt certificateToPayload blank
        (List.replicate done.length assignmentLengthSpent ++
          assignmentLengthSpent ::
            List.replicate remaining.length assignmentLengthLive ++
              SATMachineSymbol.separator :: inputLeft)
        (assignmentLengthEnd :: done.map assignmentSymbol ++
          (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool) := by
    rw [controlMachine_run_add, hstartRun]
    simpa [List.append_assoc] using hspent
  have hendRun :
      satControl.run 1
        (configAt certificateToPayload blank
          (List.replicate done.length assignmentLengthSpent ++
            assignmentLengthSpent ::
              List.replicate remaining.length assignmentLengthLive ++
                SATMachineSymbol.separator :: inputLeft)
          (assignmentLengthEnd :: done.map assignmentSymbol ++
            (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool)) =
      configAt certificateToPayload blank
        (assignmentLengthEnd ::
          List.replicate done.length assignmentLengthSpent ++
            assignmentLengthSpent ::
              List.replicate remaining.length assignmentLengthLive ++
                SATMachineSymbol.separator :: inputLeft)
        (done.map assignmentSymbol ++
          (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool) := by
    rw [controlMachine_run_one]
    exact hend
  have hprefixEnd :
      satControl.run ((1 + done.length) + 1)
        (pairingConfig inputLeft done (bit :: remaining) suffix) =
      configAt certificateToPayload blank
        (assignmentLengthEnd ::
          List.replicate done.length assignmentLengthSpent ++
            assignmentLengthSpent ::
              List.replicate remaining.length assignmentLengthLive ++
                SATMachineSymbol.separator :: inputLeft)
        (done.map assignmentSymbol ++
          (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool) := by
    rw [controlMachine_run_add, hprefix, hendRun]
  have hfull :
      satControl.run (((1 + done.length) + 1) + done.length)
        (pairingConfig inputLeft done (bit :: remaining) suffix) =
      configAt certificateToPayload blank
        ((done.map assignmentSymbol).reverse ++
          assignmentLengthEnd ::
            List.replicate done.length assignmentLengthSpent ++
              assignmentLengthSpent ::
                List.replicate remaining.length assignmentLengthLive ++
                  SATMachineSymbol.separator :: inputLeft)
        ((bit :: remaining ++ suffix).map SATMachineSymbol.ofBool) := by
    rw [controlMachine_run_add, hprefixEnd]
    simpa [List.append_assoc] using htags
  rw [show 2 * done.length + 2 = ((1 + done.length) + 1) + done.length by omega]
  rw [hfull]
  have hrep := replicate_append_same_marker done.length assignmentLengthSpent
    (List.replicate remaining.length assignmentLengthLive ++
      SATMachineSymbol.separator :: inputLeft)
  have hleft :
      (done.map assignmentSymbol).reverse ++
          assignmentLengthEnd ::
            List.replicate done.length assignmentLengthSpent ++
              assignmentLengthSpent ::
                List.replicate remaining.length assignmentLengthLive ++
                  SATMachineSymbol.separator :: inputLeft =
        (done.map assignmentSymbol).reverse ++
          assignmentLengthEnd ::
            List.replicate (done.length + 1) assignmentLengthSpent ++
              List.replicate remaining.length assignmentLengthLive ++
                SATMachineSymbol.separator :: inputLeft := by
    simpa [List.append_assoc] using
      (congrArg
        (fun xs => (done.map assignmentSymbol).reverse ++ assignmentLengthEnd :: xs)
        hrep)
  rw [hleft]



/-- Marker block traversed left after one certificate bit has been tagged. -/
def pairingReturnMarkers (done : BitString) : List SATMachineSymbol :=
  (done.map assignmentSymbol).reverse ++
    assignmentLengthEnd ::
      List.replicate (done.length + 1) assignmentLengthSpent

theorem certificateMarker_mem_pairingReturnMarkers
    (done : BitString) (marker : SATMachineSymbol)
    (hmem : marker ∈ pairingReturnMarkers done) :
    certificateMarker marker := by
  unfold pairingReturnMarkers at hmem
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hmem
  rcases hmem with htags | hend | hspent
  · have htags' : marker ∈ done.map assignmentSymbol := by
      simpa using (List.mem_reverse.mp htags)
    rcases List.mem_map.mp htags' with ⟨bit, _, rfl⟩
    exact certificateMarker_assignmentSymbol bit
  · subst marker
    exact certificateMarker_end
  · rcases hspent with ⟨_, rfl⟩
    exact certificateMarker_spent

@[simp] theorem pairingReturnMarkers_length (done : BitString) :
    (pairingReturnMarkers done).length = 2 * done.length + 2 := by
  simp [pairingReturnMarkers]
  omega

@[simp] theorem pairingReturnMarkers_reverse (done : BitString) :
    (pairingReturnMarkers done).reverse =
      List.replicate (done.length + 1) assignmentLengthSpent ++
        assignmentLengthEnd :: done.map assignmentSymbol := by
  simp [pairingReturnMarkers, List.reverse_append, List.append_assoc]


/- Converting the raw bit enters the generic leftward marker scan. -/
set_option linter.unnecessarySimpa false in
theorem step_payloadReady_raw
    (done : BitString)
    (baseHead : SATMachineSymbol)
    (baseLeft right : List SATMachineSymbol)
    (bit : Bool) :
    satControl.stepConfig
      (configAt certificateToPayload blank
        (pairingReturnMarkers done ++ baseHead :: baseLeft)
        (SATMachineSymbol.ofBool bit :: right)) =
    leftScanConfig (pairingReturnMarkers done)
      baseHead baseLeft (assignmentSymbol bit :: right) := by
  unfold pairingReturnMarkers leftScanConfig
  cases hdone : (done.map assignmentSymbol).reverse with
  | nil =>
      have hstep := step_toPayload_raw assignmentLengthEnd
        (List.replicate (done.length + 1) assignmentLengthSpent ++ baseHead :: baseLeft)
        right bit
      simpa [hdone, List.append_assoc] using hstep
  | cons marker markers =>
      have hstep := step_toPayload_raw marker
        (markers ++ assignmentLengthEnd ::
          List.replicate (done.length + 1) assignmentLengthSpent ++
            baseHead :: baseLeft)
        right bit
      simpa [hdone, List.append_assoc] using hstep

/-- One raw assignment bit is tagged and the shuttle returns to the next live marker. -/
theorem run_payload_ready_to_next_pairing
    (inputLeft : List SATMachineSymbol)
    (done remaining suffix : BitString)
    (bit : Bool) :
    satControl.run (2 * done.length + 3)
      (pairingPayloadReadyConfig inputLeft done remaining suffix bit) =
    pairingConfig inputLeft (done ++ [bit]) remaining suffix := by
  have hmarkers :
      ∀ marker ∈ pairingReturnMarkers done, certificateMarker marker := by
    intro marker hmem
    exact certificateMarker_mem_pairingReturnMarkers done marker hmem
  have hlen : 2 * done.length + 3 = 1 + (pairingReturnMarkers done).length := by
    simp
    omega
  cases remaining with
  | nil =>
      have hraw :
          satControl.run 1
            (configAt certificateToPayload blank
              (pairingReturnMarkers done ++ SATMachineSymbol.separator :: inputLeft)
              (SATMachineSymbol.ofBool bit :: suffix.map SATMachineSymbol.ofBool)) =
          leftScanConfig (pairingReturnMarkers done)
            SATMachineSymbol.separator inputLeft
            (assignmentSymbol bit :: suffix.map SATMachineSymbol.ofBool) := by
        rw [controlMachine_run_one]
        exact step_payloadReady_raw done SATMachineSymbol.separator inputLeft
          (suffix.map SATMachineSymbol.ofBool) bit
      have hscan := run_findLive_markers
        (pairingReturnMarkers done) SATMachineSymbol.separator inputLeft
        (assignmentSymbol bit :: suffix.map SATMachineSymbol.ofBool) hmarkers
      have hcombined :
          satControl.run (1 + (pairingReturnMarkers done).length)
            (configAt certificateToPayload blank
              (pairingReturnMarkers done ++ SATMachineSymbol.separator :: inputLeft)
              (SATMachineSymbol.ofBool bit :: suffix.map SATMachineSymbol.ofBool)) =
          configAt certificateFindLive blank inputLeft
            (SATMachineSymbol.separator ::
              (pairingReturnMarkers done).reverse ++
                assignmentSymbol bit :: suffix.map SATMachineSymbol.ofBool) := by
        rw [controlMachine_run_add, hraw, hscan]
      have hready :
          pairingPayloadReadyConfig inputLeft done [] suffix bit =
            configAt certificateToPayload blank
              (pairingReturnMarkers done ++ SATMachineSymbol.separator :: inputLeft)
              (SATMachineSymbol.ofBool bit :: suffix.map SATMachineSymbol.ofBool) := by
        unfold pairingPayloadReadyConfig pairingReturnMarkers
        simp [List.append_assoc]
      rw [hlen, hready, hcombined]
      unfold pairingConfig
      simp [pairingReturnMarkers_reverse, List.map_append, List.append_assoc]
      rfl
  | cons next rest =>
      have hraw :
          satControl.run 1
            (configAt certificateToPayload blank
              (pairingReturnMarkers done ++
                assignmentLengthLive ::
                  List.replicate rest.length assignmentLengthLive ++
                    SATMachineSymbol.separator :: inputLeft)
              (SATMachineSymbol.ofBool bit ::
                SATMachineSymbol.ofBool next ::
                  (rest ++ suffix).map SATMachineSymbol.ofBool)) =
          leftScanConfig (pairingReturnMarkers done)
            assignmentLengthLive
            (List.replicate rest.length assignmentLengthLive ++
              SATMachineSymbol.separator :: inputLeft)
            (assignmentSymbol bit :: SATMachineSymbol.ofBool next ::
              (rest ++ suffix).map SATMachineSymbol.ofBool) := by
        rw [controlMachine_run_one]
        have hstep := step_payloadReady_raw done assignmentLengthLive
          (List.replicate rest.length assignmentLengthLive ++
            SATMachineSymbol.separator :: inputLeft)
          (SATMachineSymbol.ofBool next ::
            (rest ++ suffix).map SATMachineSymbol.ofBool) bit
        simpa [List.append_assoc] using hstep
      have hscan := run_findLive_markers
        (pairingReturnMarkers done) assignmentLengthLive
        (List.replicate rest.length assignmentLengthLive ++
          SATMachineSymbol.separator :: inputLeft)
        (assignmentSymbol bit :: SATMachineSymbol.ofBool next ::
          (rest ++ suffix).map SATMachineSymbol.ofBool) hmarkers
      have hcombined :
          satControl.run (1 + (pairingReturnMarkers done).length)
            (configAt certificateToPayload blank
              (pairingReturnMarkers done ++
                assignmentLengthLive ::
                  List.replicate rest.length assignmentLengthLive ++
                    SATMachineSymbol.separator :: inputLeft)
              (SATMachineSymbol.ofBool bit ::
                SATMachineSymbol.ofBool next ::
                  (rest ++ suffix).map SATMachineSymbol.ofBool)) =
          configAt certificateFindLive blank
            (List.replicate rest.length assignmentLengthLive ++
              SATMachineSymbol.separator :: inputLeft)
            (assignmentLengthLive ::
              (pairingReturnMarkers done).reverse ++
                assignmentSymbol bit :: SATMachineSymbol.ofBool next ::
                  (rest ++ suffix).map SATMachineSymbol.ofBool) := by
        rw [controlMachine_run_add, hraw, hscan]
      rw [hlen]
      change satControl.run (1 + (pairingReturnMarkers done).length)
        (configAt certificateToPayload blank
          (pairingReturnMarkers done ++
            assignmentLengthLive ::
              List.replicate rest.length assignmentLengthLive ++
                SATMachineSymbol.separator :: inputLeft)
          (SATMachineSymbol.ofBool bit :: SATMachineSymbol.ofBool next ::
            (rest ++ suffix).map SATMachineSymbol.ofBool)) = _
      rw [hcombined]
      unfold pairingConfig
      simp [pairingReturnMarkers_reverse, List.map_append, List.append_assoc]
      rfl


/-- One complete pairing shuttle iteration has exact cost `4 * done.length + 5`. -/
theorem run_pairing_one
    (inputLeft : List SATMachineSymbol)
    (done remaining suffix : BitString)
    (bit : Bool) :
    satControl.run (4 * done.length + 5)
      (pairingConfig inputLeft done (bit :: remaining) suffix) =
    pairingConfig inputLeft (done ++ [bit]) remaining suffix := by
  rw [show 4 * done.length + 5 =
      (2 * done.length + 2) + (2 * done.length + 3) by omega]
  rw [controlMachine_run_add]
  rw [run_pairing_to_payload_ready]
  exact run_payload_ready_to_next_pairing inputLeft done remaining suffix bit

/-- Exact cost of pairing `remaining` bits after `doneCount` bits are already tagged. -/
def pairingCostFrom : Nat → Nat → Nat
  | _, 0 => 0
  | doneCount, remainingCount + 1 =>
      4 * doneCount + 5 + pairingCostFrom (doneCount + 1) remainingCount

@[simp] theorem pairingCostFrom_zero (doneCount : Nat) :
    pairingCostFrom doneCount 0 = 0 := rfl

@[simp] theorem pairingCostFrom_succ (doneCount remainingCount : Nat) :
    pairingCostFrom doneCount (remainingCount + 1) =
      4 * doneCount + 5 + pairingCostFrom (doneCount + 1) remainingCount := rfl

/-- Closed polynomial form of the complete pairing-shuttle cost. -/
theorem pairingCostFrom_closed (doneCount remainingCount : Nat) :
    pairingCostFrom doneCount remainingCount =
      4 * doneCount * remainingCount +
        2 * remainingCount * remainingCount +
          3 * remainingCount := by
  induction remainingCount generalizing doneCount with
  | zero => simp
  | succ remainingCount ih =>
      rw [pairingCostFrom_succ, ih]
      simp only [Nat.mul_add, Nat.add_mul]
      omega

/-- Starting from zero tagged bits, pairing `n` bits costs exactly `2n² + 3n`. -/
theorem pairingCost_zero_closed (n : Nat) :
    pairingCostFrom 0 n = 2 * n * n + 3 * n := by
  rw [pairingCostFrom_closed]
  simp

/-- The pairing shuttle normalizes every canonical assignment bit. -/
theorem run_pairing_all
    (inputLeft : List SATMachineSymbol)
    (done todo suffix : BitString) :
    satControl.run (pairingCostFrom done.length todo.length)
      (pairingConfig inputLeft done todo suffix) =
    pairingConfig inputLeft (done ++ todo) [] suffix := by
  induction todo generalizing done with
  | nil =>
      simp [pairingConfig]
  | cons bit remaining ih =>
      change satControl.run (pairingCostFrom done.length (remaining.length + 1))
        (pairingConfig inputLeft done (bit :: remaining) suffix) =
        pairingConfig inputLeft (done ++ bit :: remaining) [] suffix
      rw [pairingCostFrom_succ]
      rw [controlMachine_run_add]
      rw [run_pairing_one]
      have hrest := ih (done := done ++ [bit])
      simp only [List.length_append, List.length_singleton] at hrest
      simpa [List.append_assoc] using hrest

/-- Canonical zero-tag start reaches the fully paired separator frontier. -/
theorem run_pairing_all_from_zero
    (inputLeft : List SATMachineSymbol)
    (assignment suffix : BitString) :
    satControl.run (2 * assignment.length * assignment.length + 3 * assignment.length)
      (pairingConfig inputLeft [] assignment suffix) =
    pairingConfig inputLeft assignment [] suffix := by
  rw [← pairingCost_zero_closed assignment.length]
  simpa using run_pairing_all inputLeft [] assignment suffix


end SATMachineCertificatePhase

end OpenProblems.Complexity
