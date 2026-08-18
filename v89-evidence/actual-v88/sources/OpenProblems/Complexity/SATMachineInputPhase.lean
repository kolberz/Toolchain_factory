import OpenProblems.Complexity.SATMachineAlphabet
import OpenProblems.Complexity.SATMachinePolynomial
import OpenProblems.Complexity.EncodedSATMembership
import OpenProblems.Complexity.VerifierRectangularCNF
import OpenProblems.Universal.TapeLayout

namespace OpenProblems.Complexity

open OpenProblems
open OpenProblems.Universal

/-!
# Exact input-scan phase of the fixed encoded-SAT machine

This module proves the first complete execution phase of the concrete v74
finite control. Starting on the canonical blank cell, the typed machine enters
the input payload, scans every input bit without alteration, crosses the
separator, and arrives at the first certificate bit in state
`certificateLength`.

The result is also transferred through the trusted absorbing lowering to the
raw `FiniteMachine` execution used by the exact-machine verifier interface.
-/

/-- Typed work-alphabet encoding of the canonical verifier payload. -/
def encodedSATTypedPayload
    (input certificate : BitString) :
    List SATMachineSymbol :=
  input.map SATMachineSymbol.ofBool ++
    SATMachineSymbol.separator ::
      certificate.map SATMachineSymbol.ofBool

/-- Typed initial configuration before the payload-entry step. -/
def encodedSATTypedInitialConfig
    (input certificate : BitString) :
    Config SATMachineState SATMachineSymbol :=
  {
    state := SATMachineState.start
    tape :=
      {
        left := []
        head := SATMachineSymbol.blank
        right := encodedSATTypedPayload input certificate
      }
  }

/-- Configuration while unconsumed input bits remain under the head. -/
def encodedSATInputScanConfig
    (left : List SATMachineSymbol)
    (input certificate : BitString) :
    Config SATMachineState SATMachineSymbol :=
  match input with
  | [] =>
      {
        state := SATMachineState.seekSeparator
        tape :=
          {
            left := left
            head := SATMachineSymbol.separator
            right := certificate.map SATMachineSymbol.ofBool
          }
      }
  | bit :: remaining =>
      {
        state := SATMachineState.seekSeparator
        tape :=
          {
            left := left
            head := SATMachineSymbol.ofBool bit
            right :=
              remaining.map SATMachineSymbol.ofBool ++
                SATMachineSymbol.separator ::
                  certificate.map SATMachineSymbol.ofBool
          }
      }

/-- Configuration immediately after crossing the input/certificate separator. -/
def encodedSATCertificateLengthConfig
    (left : List SATMachineSymbol)
    (certificate : BitString) :
    Config SATMachineState SATMachineSymbol :=
  match certificate with
  | [] =>
      {
        state := SATMachineState.certificateLength
        tape :=
          {
            left := left
            head := SATMachineSymbol.blank
            right := []
          }
      }
  | bit :: remaining =>
      {
        state := SATMachineState.certificateLength
        tape :=
          {
            left := left
            head := SATMachineSymbol.ofBool bit
            right := remaining.map SATMachineSymbol.ofBool
          }
      }

/-- The start state enters the first input cell in one step. -/
theorem encodedSATTyped_step_initial
    (input certificate : BitString) :
    encodedSATFiniteControl.control.stepConfig
        (encodedSATTypedInitialConfig input certificate) =
      encodedSATInputScanConfig
        [SATMachineSymbol.blank]
        input certificate := by
  cases input <;> rfl

/-- One input bit is preserved while the scanner advances right. -/
theorem encodedSATTyped_step_input_bit
    (left : List SATMachineSymbol)
    (bit : Bool)
    (remaining certificate : BitString) :
    encodedSATFiniteControl.control.stepConfig
        (encodedSATInputScanConfig
          left (bit :: remaining) certificate) =
      encodedSATInputScanConfig
        (SATMachineSymbol.ofBool bit :: left)
        remaining certificate := by
  cases bit <;> cases remaining <;> rfl

/-- The scanner consumes exactly the input length and stops on the separator. -/
theorem encodedSATTyped_run_input
    (left : List SATMachineSymbol)
    (input certificate : BitString) :
    encodedSATFiniteControl.control.run
        input.length
        (encodedSATInputScanConfig left input certificate) =
      encodedSATInputScanConfig
        ((input.map SATMachineSymbol.ofBool).reverse ++ left)
        [] certificate := by
  induction input generalizing left with
  | nil =>
      rfl
  | cons bit remaining ih =>
      rw [List.length_cons]
      change
        encodedSATFiniteControl.control.run remaining.length
            (encodedSATFiniteControl.control.stepConfig
              (encodedSATInputScanConfig left (bit :: remaining) certificate)) = _
      rw [encodedSATTyped_step_input_bit]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (SATMachineSymbol.ofBool bit :: left)

/-- Crossing the separator enters the certificate unary-length phase. -/
theorem encodedSATTyped_step_separator
    (left : List SATMachineSymbol)
    (certificate : BitString) :
    encodedSATFiniteControl.control.stepConfig
        (encodedSATInputScanConfig left [] certificate) =
      encodedSATCertificateLengthConfig
        (SATMachineSymbol.separator :: left)
        certificate := by
  cases certificate <;> rfl

/--
The complete input phase takes one entry step, one step per input bit, and one
separator step.
-/
theorem encodedSATTyped_run_to_certificateLength
    (input certificate : BitString) :
    encodedSATFiniteControl.control.run
        (input.length + 2)
        (encodedSATTypedInitialConfig input certificate) =
      encodedSATCertificateLengthConfig
        (SATMachineSymbol.separator ::
          ((input.map SATMachineSymbol.ofBool).reverse ++
            [SATMachineSymbol.blank]))
        certificate := by
  have hscan :
      ∀ (xs : BitString) (left : List SATMachineSymbol),
        encodedSATFiniteControl.control.run
            (xs.length + 1)
            (encodedSATInputScanConfig left xs certificate) =
          encodedSATCertificateLengthConfig
            (SATMachineSymbol.separator ::
              ((xs.map SATMachineSymbol.ofBool).reverse ++ left))
            certificate := by
    intro xs
    induction xs with
    | nil =>
        intro left
        change
          encodedSATFiniteControl.control.stepConfig
              (encodedSATInputScanConfig left [] certificate) = _
        exact encodedSATTyped_step_separator left certificate
    | cons bit remaining ih =>
        intro left
        rw [List.length_cons]
        change
          encodedSATFiniteControl.control.run
              (remaining.length + 1)
              (encodedSATFiniteControl.control.stepConfig
                (encodedSATInputScanConfig
                  left (bit :: remaining) certificate)) = _
        rw [encodedSATTyped_step_input_bit]
        simpa [List.reverse_cons, List.append_assoc] using
          ih (SATMachineSymbol.ofBool bit :: left)
  change
    encodedSATFiniteControl.control.run
        (input.length + 1)
        (encodedSATFiniteControl.control.stepConfig
          (encodedSATTypedInitialConfig input certificate)) = _
  rw [encodedSATTyped_step_initial]
  exact hscan input [SATMachineSymbol.blank]

/-- The typed input phase commutes through raw absorbing lowering. -/
theorem encodedSATRaw_run_to_certificateLength
    (input certificate : BitString) :
    encodedSATFiniteMachine.toDTM.run
        (input.length + 2)
        (FiniteControlMachine.encodeConfig
          (encodedSATTypedInitialConfig input certificate)) =
      FiniteControlMachine.encodeConfig
        (encodedSATCertificateLengthConfig
          (SATMachineSymbol.separator ::
            ((input.map SATMachineSymbol.ofBool).reverse ++
              [SATMachineSymbol.blank]))
          certificate) := by
  have h :=
    FiniteControlMachine.lowerAbsorbing_run_commutes
      encodedSATFiniteControl
      (input.length + 2)
      (encodedSATTypedInitialConfig input certificate)
  rw [encodedSATTyped_run_to_certificateLength] at h
  exact h

/-- Concrete rectangular verifier program carried by the fixed SAT machine. -/
def encodedSATRectangularProgram :
    RectangularMachineVerifierProgram where
  machine := encodedSATFiniteMachine
  witnessBound := CNF.encodedSATWitnessPolynomial
  timeBound := prefixSATMachineTimePolynomial
  symbolCapacity := encodedSATFiniteMachine_symbolCapacity

@[simp]
theorem encodedSATRectangularProgram_machine :
    encodedSATRectangularProgram.machine =
      encodedSATFiniteMachine :=
  rfl

@[simp]
theorem encodedSATRectangularProgram_witnessBound :
    encodedSATRectangularProgram.witnessBound =
      CNF.encodedSATWitnessPolynomial :=
  rfl

@[simp]
theorem encodedSATRectangularProgram_timeBound :
    encodedSATRectangularProgram.timeBound =
      prefixSATMachineTimePolynomial :=
  rfl

end OpenProblems.Complexity
