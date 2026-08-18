import OpenProblems.Complexity.Polynomial

namespace OpenProblems.Complexity

/-!
# Coarse execution budget for the fixed prefix-SAT machine

The fused one-tape verifier uses repeated full-payload shuttles.  Its phase
proofs target a deliberately loose quartic budget.  Keeping the polynomial
separate from the transition table makes the eventual resource theorem a
plain inequality rather than part of the machine definition.
-/

/-- The shifted payload-size polynomial `x + 4`. -/
def prefixSATShiftPolynomial : NatPolynomial :=
  .add .variable (.constant 4)

/-- Safe quartic budget `128 * (x + 4)^4`. -/
def prefixSATMachineTimePolynomial : NatPolynomial :=
  .mul
    (.constant 128)
    ((NatPolynomial.power 4).compose
      prefixSATShiftPolynomial)

@[simp]
theorem prefixSATShiftPolynomial_eval
    (size : Nat) :
    prefixSATShiftPolynomial.eval size =
      size + 4 :=
  rfl

@[simp]
theorem prefixSATMachineTimePolynomial_eval
    (size : Nat) :
    prefixSATMachineTimePolynomial.eval size =
      128 * (size + 4) ^ 4 := by
  simp [prefixSATMachineTimePolynomial,
    prefixSATShiftPolynomial]

theorem prefixSATMachineTimePolynomial_pos
    (size : Nat) :
    0 < prefixSATMachineTimePolynomial.eval size := by
  rw [prefixSATMachineTimePolynomial_eval]
  exact
    Nat.mul_pos (by decide)
      (Nat.pow_pos (by omega))

theorem prefixSATMachineTimePolynomial_mono
    {left right : Nat}
    (hle : left ≤ right) :
    prefixSATMachineTimePolynomial.eval left ≤
      prefixSATMachineTimePolynomial.eval right :=
  NatPolynomial.eval_mono
    prefixSATMachineTimePolynomial hle

end OpenProblems.Complexity
