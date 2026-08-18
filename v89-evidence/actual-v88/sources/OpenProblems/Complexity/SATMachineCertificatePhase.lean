import OpenProblems.Complexity.SATMachineInputPhase
import OpenProblems.Complexity.SATMachineCodecLayout

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

namespace SATMachineCertificatePhase

open SATMachineSymbol SATMachineState

abbrev satControl : ControlMachine SATMachineState SATMachineSymbol :=
  encodedSATFiniteControl.control

/-- Work-alphabet encoding used once a certificate payload bit is normalized. -/
def assignmentSymbol : Bool → SATMachineSymbol
  | false => SATMachineSymbol.assignmentFalse
  | true => SATMachineSymbol.assignmentTrue

@[simp] theorem assignmentSymbol_false : assignmentSymbol false = SATMachineSymbol.assignmentFalse := rfl
@[simp] theorem assignmentSymbol_true : assignmentSymbol true = SATMachineSymbol.assignmentTrue := rfl


private theorem replicate_append_same
    {α : Type} (n : Nat) (a : α) (tail : List α) :
    List.replicate n a ++ a :: tail =
      List.replicate (n + 1) a ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact congrArg (fun xs => a :: xs) ih

/-- State reached after scanning the unary certificate-length prefix. -/
def unaryScannedConfig
    (left : List SATMachineSymbol)
    (count : Nat)
    (payload : BitString) :
    Config SATMachineState SATMachineSymbol :=
  {
    state := SATMachineState.certificateLength
    tape := {
      left := List.replicate count SATMachineSymbol.assignmentLengthLive ++ left
      head := SATMachineSymbol.rawFalse
      right := payload.map SATMachineSymbol.ofBool
    }
  }

/-- Scanning a canonical unary prefix consumes exactly its unary length. -/
theorem run_unary_prefix
    (left : List SATMachineSymbol)
    (count : Nat)
    (payload : BitString) :
    satControl.run count
        (encodedSATCertificateLengthConfig
          left
          (List.replicate count true ++ false :: payload)) =
      unaryScannedConfig left count payload := by
  induction count generalizing left with
  | zero =>
      rfl
  | succ count ih =>
      rw [List.replicate_succ]
      change
        satControl.run (count + 1)
          (encodedSATCertificateLengthConfig
            left
            (true :: (List.replicate count true ++ false :: payload))) = _
      change
        satControl.run count
          (satControl.stepConfig
            (encodedSATCertificateLengthConfig
              left
              (true :: (List.replicate count true ++ false :: payload)))) = _
      have hstep :
          satControl.stepConfig
              (encodedSATCertificateLengthConfig
                left
                (true :: (List.replicate count true ++ false :: payload))) =
            encodedSATCertificateLengthConfig
              (SATMachineSymbol.assignmentLengthLive :: left)
              (List.replicate count true ++ false :: payload) := by
        cases count <;> rfl
      rw [hstep, ih]
      unfold unaryScannedConfig
      congr 2
      exact replicate_append_same count SATMachineSymbol.assignmentLengthLive left


/-- Pairing state: `done` certificate bits have been tagged and `todo` remain. -/
def pairingConfig
    (inputLeft : List SATMachineSymbol)
    (done todo suffix : BitString) :
    Config SATMachineState SATMachineSymbol :=
  match todo with
  | [] =>
      {
        state := SATMachineState.certificateFindLive
        tape := {
          left := inputLeft
          head := SATMachineSymbol.separator
          right :=
            List.replicate done.length SATMachineSymbol.assignmentLengthSpent ++
              SATMachineSymbol.assignmentLengthEnd ::
                done.map assignmentSymbol ++
                  suffix.map SATMachineSymbol.ofBool
        }
      }
  | bit :: remaining =>
      {
        state := SATMachineState.certificateFindLive
        tape := {
          left :=
            List.replicate remaining.length SATMachineSymbol.assignmentLengthLive ++
              SATMachineSymbol.separator :: inputLeft
          head := SATMachineSymbol.assignmentLengthLive
          right :=
            List.replicate done.length SATMachineSymbol.assignmentLengthSpent ++
              SATMachineSymbol.assignmentLengthEnd ::
                done.map assignmentSymbol ++
                  (bit :: remaining ++ suffix).map SATMachineSymbol.ofBool
        }
      }



/-- The unary terminator enters the certificate-bit pairing loop. -/
theorem step_unary_terminator
    (inputLeft : List SATMachineSymbol)
    (assignment suffix : BitString) :
    satControl.stepConfig
        (unaryScannedConfig
          (SATMachineSymbol.separator :: inputLeft)
          assignment.length
          (assignment ++ suffix)) =
      pairingConfig inputLeft [] assignment suffix := by
  cases assignment with
  | nil =>
      rfl
  | cons bit remaining =>
      unfold unaryScannedConfig pairingConfig
      simp only [List.length_cons]
      rw [List.replicate_succ]
      cases bit <;> rfl

/--
A canonically encoded assignment reaches the pairing loop after exactly its
unary-prefix length plus the terminator step.
-/
theorem run_encodedAssignment_to_pairing
    (inputLeft : List SATMachineSymbol)
    (assignment suffix : BitString) :
    satControl.run
        (assignment.length + 1)
        (encodedSATCertificateLengthConfig
          (SATMachineSymbol.separator :: inputLeft)
          (CNF.encodeAssignment assignment ++ suffix)) =
      pairingConfig inputLeft [] assignment suffix := by
  rw [CNF.encodeAssignment_physical_layout]
  simp only [List.append_assoc, List.cons_append]
  rw [controlMachine_run_add]
  rw [run_unary_prefix]
  rw [controlMachine_run_one]
  exact step_unary_terminator inputLeft assignment suffix


/--
Compose the verified input scan with the verified canonical certificate-prefix
scan.  The machine is now at the first certificate-pairing iteration.
-/
theorem run_typed_to_pairing
    (input assignment suffix : BitString) :
    satControl.run
        ((input.length + 2) + (assignment.length + 1))
        (encodedSATTypedInitialConfig
          input
          (CNF.encodeAssignment assignment ++ suffix)) =
      pairingConfig
        ((input.map SATMachineSymbol.ofBool).reverse ++
          [SATMachineSymbol.blank])
        [] assignment suffix := by
  rw [controlMachine_run_add]
  have hinput :=
    encodedSATTyped_run_to_certificateLength
      input (CNF.encodeAssignment assignment ++ suffix)
  change
    satControl.run (input.length + 2)
        (encodedSATTypedInitialConfig
          input (CNF.encodeAssignment assignment ++ suffix)) = _
    at hinput
  rw [hinput]
  exact
    run_encodedAssignment_to_pairing
      ((input.map SATMachineSymbol.ofBool).reverse ++
        [SATMachineSymbol.blank])
      assignment suffix

/--
The same composed prefix phase after trusted absorbing lowering to the raw
finite machine used by the polynomial verifier interface.
-/
theorem run_raw_to_pairing
    (input assignment suffix : BitString) :
    encodedSATFiniteMachine.toDTM.run
        ((input.length + 2) + (assignment.length + 1))
        (FiniteControlMachine.encodeConfig
          (encodedSATTypedInitialConfig
            input
            (CNF.encodeAssignment assignment ++ suffix))) =
      FiniteControlMachine.encodeConfig
        (pairingConfig
          ((input.map SATMachineSymbol.ofBool).reverse ++
            [SATMachineSymbol.blank])
          [] assignment suffix) := by
  unfold encodedSATFiniteMachine
  calc
    _ = FiniteControlMachine.encodeConfig
        (satControl.run
          ((input.length + 2) + (assignment.length + 1))
          (encodedSATTypedInitialConfig
            input
            (CNF.encodeAssignment assignment ++ suffix))) :=
      FiniteControlMachine.lowerAbsorbing_run_commutes
        encodedSATFiniteControl
        ((input.length + 2) + (assignment.length + 1))
        (encodedSATTypedInitialConfig
          input
          (CNF.encodeAssignment assignment ++ suffix))
    _ = _ := congrArg FiniteControlMachine.encodeConfig
      (run_typed_to_pairing input assignment suffix)

end SATMachineCertificatePhase

end OpenProblems.Complexity
