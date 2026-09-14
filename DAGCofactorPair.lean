import DAGSupportSensitive

namespace DAGRestrictionUpdate

/-- Compute both Boolean cofactors in one structural traversal. In a concrete
hash-consed evaluator, the two components may share every unchanged node. -/
def cofactorPair (v : Nat) : Expr → Expr × Expr
  | .const c => (.const c, .const c)
  | .var x =>
      if x = v then (.const 0, .const 1) else (.var x, .var x)
  | .add a b =>
      let pa := cofactorPair v a
      let pb := cofactorPair v b
      (.add pa.1 pb.1, .add pa.2 pb.2)
  | .mul a b =>
      let pa := cofactorPair v a
      let pb := cofactorPair v b
      (.mul pa.1 pb.1, .mul pa.2 pb.2)

/-- The paired traversal is extensionally identical to the two independent
structural restrictions. -/
theorem cofactorPair_eq_restrictions (v : Nat) (e : Expr) :
    cofactorPair v e = (restrict v 0 e, restrict v 1 e) := by
  induction e with
  | const c =>
      rfl
  | var x =>
      by_cases h : x = v
      · simp [cofactorPair, restrict, h]
      · simp [cofactorPair, restrict, h]
  | add a b iha ihb =>
      simp [cofactorPair, restrict, iha, ihb]
  | mul a b iha ihb =>
      simp [cofactorPair, restrict, iha, ihb]

/-- First paired output is the zero cofactor. -/
theorem cofactorPair_fst (v : Nat) (e : Expr) :
    (cofactorPair v e).1 = restrict v 0 e := by
  rw [cofactorPair_eq_restrictions]

/-- Second paired output is the one cofactor. -/
theorem cofactorPair_snd (v : Nat) (e : Expr) :
    (cofactorPair v e).2 = restrict v 1 e := by
  rw [cofactorPair_eq_restrictions]

/-- Exact range avoidance: when `v` is absent, both outputs are the original
subexpression. A canonical DAG representation can therefore reuse the same node
for both outputs with no descendant rebuilding. -/
theorem cofactorPair_eq_self_of_free
    (v : Nat) (e : Expr) (hfree : FreeOf v e) :
    cofactorPair v e = (e, e) := by
  rw [cofactorPair_eq_restrictions]
  rcases both_cofactors_eq_self_of_free v e hfree with ⟨h0, h1⟩
  simp [h0, h1]

/-- Construct the update from the paired traversal. -/
def updateFromPair (v : Nat) (e : Expr) : Expr :=
  let p := cofactorPair v e
  .add p.1 p.2

/-- One-pass paired cofactoring computes the same update syntax. -/
theorem updateFromPair_eq_update (v : Nat) (e : Expr) :
    updateFromPair v e = update v e := by
  simp [updateFromPair, update, cofactorPair_fst, cofactorPair_snd]

/-- Consequently, the paired traversal computes exact marginalization. -/
theorem eval_updateFromPair_eq_marginalize
    (ρ : Nat → Nat) (v : Nat) (e : Expr) :
    eval ρ (updateFromPair v e) = marginalize ρ v e := by
  rw [updateFromPair_eq_update]
  exact eval_update_eq_marginalize ρ v e

#print axioms cofactorPair_eq_restrictions
#print axioms cofactorPair_eq_self_of_free
#print axioms updateFromPair_eq_update
#print axioms eval_updateFromPair_eq_marginalize

end DAGRestrictionUpdate
