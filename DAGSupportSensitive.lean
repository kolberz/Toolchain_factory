import DAGRestrictionUpdate

namespace DAGRestrictionUpdate

/-- `FreeOf v e` means coordinate `v` is absent from the syntactic support of
`e`. Keeping this structural avoids importing a finite-set representation into
the trusted statement. -/
def FreeOf (v : Nat) : Expr → Prop
  | .const _ => True
  | .var x => x ≠ v
  | .add a b => FreeOf v a ∧ FreeOf v b
  | .mul a b => FreeOf v a ∧ FreeOf v b

/-- If coordinate `v` is absent from a subexpression, restricting that
coordinate leaves the subexpression structurally unchanged. In a hash-consed
implementation this is the exact condition under which the original node can be
reused rather than rebuilt. -/
theorem restrict_eq_self_of_free
    (v b : Nat) (e : Expr)
    (hfree : FreeOf v e) :
    restrict v b e = e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      simp only [FreeOf] at hfree
      simp [restrict, hfree]
  | add a c iha ihc =>
      simp only [FreeOf] at hfree
      rcases hfree with ⟨ha, hc⟩
      simp [restrict, iha ha, ihc hc]
  | mul a c iha ihc =>
      simp only [FreeOf] at hfree
      rcases hfree with ⟨ha, hc⟩
      simp [restrict, iha ha, ihc hc]

/-- Both Boolean cofactors reuse a `v`-free subexpression. -/
theorem both_cofactors_eq_self_of_free
    (v : Nat) (e : Expr)
    (hfree : FreeOf v e) :
    restrict v 0 e = e ∧ restrict v 1 e = e := by
  constructor
  · exact restrict_eq_self_of_free v 0 e hfree
  · exact restrict_eq_self_of_free v 1 e hfree

/-- Number of syntax nodes in the `v`-dependent ancestral cone. A compound node
belongs to the cone exactly when at least one child has a nonempty dependent
cone. This is an abstract accounting object, not an allocator measurement. -/
def dependentConeSize (v : Nat) : Expr → Nat
  | .const _ => 0
  | .var x => if x = v then 1 else 0
  | .add a b =>
      let ca := dependentConeSize v a
      let cb := dependentConeSize v b
      if ca = 0 ∧ cb = 0 then 0 else 1 + ca + cb
  | .mul a b =>
      let ca := dependentConeSize v a
      let cb := dependentConeSize v b
      if ca = 0 ∧ cb = 0 then 0 else 1 + ca + cb

/-- A support-free subtree contributes no nodes to the dependent cone. -/
theorem dependentConeSize_eq_zero_of_free
    (v : Nat) (e : Expr)
    (hfree : FreeOf v e) :
    dependentConeSize v e = 0 := by
  induction e with
  | const c =>
      rfl
  | var x =>
      simp only [FreeOf] at hfree
      simp [dependentConeSize, hfree]
  | add a c iha ihc =>
      simp only [FreeOf] at hfree
      rcases hfree with ⟨ha, hc⟩
      simp [dependentConeSize, iha ha, ihc hc]
  | mul a c iha ihc =>
      simp only [FreeOf] at hfree
      rcases hfree with ⟨ha, hc⟩
      simp [dependentConeSize, iha ha, ihc hc]

/-- The dependent cone never exceeds the full tree syntax. -/
theorem dependentConeSize_le_treeSize (v : Nat) (e : Expr) :
    dependentConeSize v e ≤ treeSize e := by
  induction e with
  | const c =>
      simp [dependentConeSize, treeSize]
  | var x =>
      by_cases h : x = v
      · simp [dependentConeSize, treeSize, h]
      · simp [dependentConeSize, treeSize, h]
  | add a c iha ihc =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v c = 0
      · simp [dependentConeSize, treeSize, h]
      · simpa [dependentConeSize, treeSize, h] using
          Nat.add_le_add (Nat.add_le_add_left iha 1) ihc
  | mul a c iha ihc =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v c = 0
      · simp [dependentConeSize, treeSize, h]
      · simpa [dependentConeSize, treeSize, h] using
          Nat.add_le_add (Nat.add_le_add_left iha 1) ihc

/-- Abstract allocation budget for an implementation that reuses every node
outside the dependent cone and rebuilds at most one node per affected node for
each Boolean cofactor, plus the final `add` node. -/
def supportSensitiveUpdateBudget (v : Nat) (e : Expr) : Nat :=
  1 + 2 * dependentConeSize v e

/-- Range avoidance collapses the abstract update budget to the final add node
when the eliminated variable is absent. -/
theorem supportSensitiveUpdateBudget_eq_one_of_free
    (v : Nat) (e : Expr)
    (hfree : FreeOf v e) :
    supportSensitiveUpdateBudget v e = 1 := by
  simp [supportSensitiveUpdateBudget,
    dependentConeSize_eq_zero_of_free v e hfree]

/-- The support-sensitive budget refines the elementary whole-tree duplication
bound. Connecting this budget to actual allocated DAG nodes is a separate
implementation-correctness obligation. -/
theorem supportSensitiveUpdateBudget_le_treeBound
    (v : Nat) (e : Expr) :
    supportSensitiveUpdateBudget v e ≤ 1 + 2 * treeSize e := by
  unfold supportSensitiveUpdateBudget
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 (dependentConeSize_le_treeSize v e)) 1

#print axioms restrict_eq_self_of_free
#print axioms both_cofactors_eq_self_of_free
#print axioms dependentConeSize_eq_zero_of_free
#print axioms dependentConeSize_le_treeSize
#print axioms supportSensitiveUpdateBudget_eq_one_of_free
#print axioms supportSensitiveUpdateBudget_le_treeBound

end DAGRestrictionUpdate
