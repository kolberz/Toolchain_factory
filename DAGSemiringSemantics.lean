import DAGRestrictionUpdate

namespace DAGRestrictionUpdate

section SemiringSemantics

variable {R : Type*} [Semiring R]

/-- Interpret the same syntax in an arbitrary semiring. Natural constants are
mapped through the canonical `Nat` cast; variables are supplied by `ρ`. -/
def evalSemiring (ρ : Nat → R) : Expr → R
  | .const c => (c : R)
  | .var x => ρ x
  | .add a b => evalSemiring ρ a + evalSemiring ρ b
  | .mul a b => evalSemiring ρ a * evalSemiring ρ b

/-- Override one coordinate in an arbitrary semiring-valued environment. -/
def assignSemiring (ρ : Nat → R) (v : Nat) (b : R) : Nat → R :=
  fun x => if x = v then b else ρ x

/-- Structural restriction is exact coordinate substitution in every semiring.
No distributive expansion or normal-form conversion is used. -/
theorem evalSemiring_restrict
    (ρ : Nat → R) (v b : Nat) (e : Expr) :
    evalSemiring ρ (restrict v b e) =
      evalSemiring (assignSemiring ρ v (b : R)) e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      by_cases h : x = v
      · subst x
        simp [restrict, evalSemiring, assignSemiring]
      · simp [restrict, evalSemiring, assignSemiring, h]
  | add a c iha ihc =>
      simp [restrict, evalSemiring, iha, ihc]
  | mul a c iha ihc =>
      simp [restrict, evalSemiring, iha, ihc]

/-- Two-point marginalization in an arbitrary semiring. -/
def marginalizeSemiring (ρ : Nat → R) (v : Nat) (e : Expr) : R :=
  evalSemiring (assignSemiring ρ v (0 : R)) e +
  evalSemiring (assignSemiring ρ v (1 : R)) e

/-- Generalized Shannon/cofactor theorem: the structural update computes exact
Boolean-coordinate marginalization over every semiring. -/
theorem evalSemiring_update_eq_marginalize
    (ρ : Nat → R) (v : Nat) (e : Expr) :
    evalSemiring ρ (update v e) = marginalizeSemiring ρ v e := by
  simp [update, marginalizeSemiring, evalSemiring, evalSemiring_restrict]

#print axioms evalSemiring_restrict
#print axioms evalSemiring_update_eq_marginalize

end SemiringSemantics

end DAGRestrictionUpdate
