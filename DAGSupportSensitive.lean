import DAGRestrictionUpdate

namespace DAGRestrictionUpdate

/-- Variables syntactically occurring below an expression node. -/
def support : Expr → Finset Nat
  | .const _ => ∅
  | .var x => {x}
  | .add a b => support a ∪ support b
  | .mul a b => support a ∪ support b

/-- If coordinate `v` is absent from a subexpression's support, restricting that
coordinate leaves the subexpression structurally unchanged. In a hash-consed
implementation this is the exact condition under which the original node may be
reused rather than rebuilt. -/
theorem restrict_eq_self_of_not_mem_support
    (v b : Nat) (e : Expr)
    (hfree : v ∉ support e) :
    restrict v b e = e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      simp only [support, Finset.mem_singleton] at hfree
      have hx : x ≠ v := by
        intro hxv
        exact hfree hxv.symm
      simp [restrict, hx]
  | add a c iha ihc =>
      simp only [support, Finset.mem_union, not_or] at hfree
      rcases hfree with ⟨ha, hc⟩
      simp [restrict, iha ha, ihc hc]
  | mul a c iha ihc =>
      simp only [support, Finset.mem_union, not_or] at hfree
      rcases hfree with ⟨ha, hc⟩
      simp [restrict, iha ha, ihc hc]

/-- Both Boolean cofactors reuse a `v`-free subexpression. -/
theorem both_cofactors_eq_self_of_not_mem_support
    (v : Nat) (e : Expr)
    (hfree : v ∉ support e) :
    restrict v 0 e = e ∧ restrict v 1 e = e := by
  constructor
  · exact restrict_eq_self_of_not_mem_support v 0 e hfree
  · exact restrict_eq_self_of_not_mem_support v 1 e hfree

/-- Number of syntax nodes in the `v`-dependent ancestral cone. This is a
representation-independent upper-bound ingredient; it is not itself an
allocator measurement. -/
def dependentConeSize (v : Nat) : Expr → Nat
  | .const _ => 0
  | .var x => if x = v then 1 else 0
  | .add a b =>
      if v ∈ support a ∪ support b then
        1 + dependentConeSize v a + dependentConeSize v b
      else
        0
  | .mul a b =>
      if v ∈ support a ∪ support b then
        1 + dependentConeSize v a + dependentConeSize v b
      else
        0

/-- A support-free subtree contributes no nodes to the dependent cone. -/
theorem dependentConeSize_eq_zero_of_not_mem_support
    (v : Nat) (e : Expr)
    (hfree : v ∉ support e) :
    dependentConeSize v e = 0 := by
  induction e with
  | const c =>
      rfl
  | var x =>
      simp only [support, Finset.mem_singleton] at hfree
      have hx : x ≠ v := by
        intro hxv
        exact hfree hxv.symm
      simp [dependentConeSize, hx]
  | add a c iha ihc =>
      simp only [support, Finset.mem_union, not_or] at hfree
      rcases hfree with ⟨ha, hc⟩
      have hu : v ∉ support a ∪ support c := by
        simp [ha, hc]
      simp [dependentConeSize, hu]
  | mul a c iha ihc =>
      simp only [support, Finset.mem_union, not_or] at hfree
      rcases hfree with ⟨ha, hc⟩
      have hu : v ∉ support a ∪ support c := by
        simp [ha, hc]
      simp [dependentConeSize, hu]

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
      by_cases h : v ∈ support a ∪ support c
      · simp [dependentConeSize, treeSize, h]
        omega
      · simp [dependentConeSize, treeSize, h]
  | mul a c iha ihc =>
      by_cases h : v ∈ support a ∪ support c
      · simp [dependentConeSize, treeSize, h]
        omega
      · simp [dependentConeSize, treeSize, h]

/-- Abstract allocation budget for an implementation that reuses every node
outside the dependent cone and rebuilds at most one node per affected node for
each Boolean cofactor, plus the final `add` node. -/
def supportSensitiveUpdateBudget (v : Nat) (e : Expr) : Nat :=
  1 + 2 * dependentConeSize v e

/-- Range avoidance collapses the abstract update budget to the final add node
when the eliminated variable is absent. -/
theorem supportSensitiveUpdateBudget_eq_one_of_not_mem_support
    (v : Nat) (e : Expr)
    (hfree : v ∉ support e) :
    supportSensitiveUpdateBudget v e = 1 := by
  simp [supportSensitiveUpdateBudget,
    dependentConeSize_eq_zero_of_not_mem_support v e hfree]

/-- The support-sensitive budget refines the elementary whole-tree duplication
bound. Connecting this budget to actual allocated DAG nodes is a separate
implementation-correctness obligation. -/
theorem supportSensitiveUpdateBudget_le_treeBound
    (v : Nat) (e : Expr) :
    supportSensitiveUpdateBudget v e ≤ 1 + 2 * treeSize e := by
  unfold supportSensitiveUpdateBudget
  have h := dependentConeSize_le_treeSize v e
  omega

#print axioms restrict_eq_self_of_not_mem_support
#print axioms both_cofactors_eq_self_of_not_mem_support
#print axioms dependentConeSize_eq_zero_of_not_mem_support
#print axioms dependentConeSize_le_treeSize
#print axioms supportSensitiveUpdateBudget_eq_one_of_not_mem_support
#print axioms supportSensitiveUpdateBudget_le_treeBound

end DAGRestrictionUpdate
