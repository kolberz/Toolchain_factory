import DAGReferenceAllocator

namespace DAGRestrictionUpdate

/-- A list of affected syntax occurrences. Unlike `dependentConeSize`, this
retains the actual expression at each affected occurrence so that a subsequent
computable deduplication step can model hash-consing by structural node identity. -/
def dependentOccurrenceNodes (v : Nat) : Expr → List Expr
  | .const _ => []
  | .var x =>
      if x = v then [.var x] else []
  | .add a b =>
      if _h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0 then
        []
      else
        .add a b :: (dependentOccurrenceNodes v a ++ dependentOccurrenceNodes v b)
  | .mul a b =>
      if _h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0 then
        []
      else
        .mul a b :: (dependentOccurrenceNodes v a ++ dependentOccurrenceNodes v b)

/-- The occurrence list is an executable witness for the tree-level dependent
cone count. -/
theorem dependentOccurrenceNodes_length (v : Nat) (e : Expr) :
    (dependentOccurrenceNodes v e).length = dependentConeSize v e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      by_cases h : x = v
      · simp [dependentOccurrenceNodes, dependentConeSize, h]
      · simp [dependentOccurrenceNodes, dependentConeSize, h]
  | add a b iha ihb =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simp [dependentOccurrenceNodes, dependentConeSize, h]
      · simp [dependentOccurrenceNodes, dependentConeSize, h, iha, ihb]
        exact
          calc
            dependentConeSize v a + (dependentConeSize v b + 1) =
                (dependentConeSize v a + dependentConeSize v b) + 1 :=
              (Nat.add_assoc _ _ _).symm
            _ = 1 + (dependentConeSize v a + dependentConeSize v b) :=
              Nat.add_comm _ _
            _ = (1 + dependentConeSize v a) + dependentConeSize v b :=
              (Nat.add_assoc _ _ _).symm
  | mul a b iha ihb =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simp [dependentOccurrenceNodes, dependentConeSize, h]
      · simp [dependentOccurrenceNodes, dependentConeSize, h, iha, ihb]
        exact
          calc
            dependentConeSize v a + (dependentConeSize v b + 1) =
                (dependentConeSize v a + dependentConeSize v b) + 1 :=
              (Nat.add_assoc _ _ _).symm
            _ = 1 + (dependentConeSize v a + dependentConeSize v b) :=
              Nat.add_comm _ _
            _ = (1 + dependentConeSize v a) + dependentConeSize v b :=
              (Nat.add_assoc _ _ _).symm

/-- Executable structural deduplication. The retained representative is the last
occurrence of each structurally equal expression. This choice is deterministic
and uses the derived computational `DecidableEq Expr`. -/
def dedupNodes : List Expr → List Expr
  | [] => []
  | x :: xs =>
      if x ∈ xs then dedupNodes xs else x :: dedupNodes xs

/-- Structural deduplication never increases list length. This proof deliberately
avoids simplifier-driven reasoning about list membership so the theorem does not
acquire a classical-choice dependency. -/
theorem dedupNodes_length_le (xs : List Expr) :
    (dedupNodes xs).length ≤ xs.length := by
  induction xs with
  | nil =>
      exact Nat.le_refl 0
  | cons x xs ih =>
      unfold dedupNodes
      split
      · exact Nat.le_succ_of_le ih
      · simp only [List.length_cons]
        exact Nat.succ_le_succ ih

/-- Hash-consed dependent DAG nodes, represented by a deterministic executable
structural deduplication of the affected occurrences. -/
def dagDependentNodes (v : Nat) (e : Expr) : List Expr :=
  dedupNodes (dependentOccurrenceNodes v e)

/-- Number of distinct affected DAG nodes under structural hash-consing. -/
def dagDependentCount (v : Nat) (e : Expr) : Nat :=
  (dagDependentNodes v e).length

/-- Deduplication never increases the affected-node count. -/
theorem dagDependentCount_le_dependentConeSize (v : Nat) (e : Expr) :
    dagDependentCount v e ≤ dependentConeSize v e := by
  calc
    dagDependentCount v e =
        (dedupNodes (dependentOccurrenceNodes v e)).length := rfl
    _ ≤ (dependentOccurrenceNodes v e).length :=
      dedupNodes_length_le _
    _ = dependentConeSize v e := dependentOccurrenceNodes_length v e

/-- Allocation events for the shared evaluator carry the structural node being
materialized, making this an executable memoized trace rather than a numeric
cost oracle. -/
inductive SharedAllocationEvent where
  | cofactorZero : Expr → SharedAllocationEvent
  | cofactorOne : Expr → SharedAllocationEvent
  | finalAdd : SharedAllocationEvent
  deriving Repr, DecidableEq

/-- Emit exactly two fresh nodes for every distinct affected DAG node. -/
def sharedPairEvents : List Expr → List SharedAllocationEvent
  | [] => []
  | e :: es =>
      .cofactorZero e :: .cofactorOne e :: sharedPairEvents es

/-- Exact size of the memoized paired-cofactor trace. -/
theorem sharedPairEvents_length (xs : List Expr) :
    (sharedPairEvents xs).length = 2 * xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [sharedPairEvents, ih]
      exact
        calc
          (2 * xs.length + 1) + 1 = 2 * xs.length + (1 + 1) :=
            Nat.add_assoc _ _ _
          _ = 2 * xs.length + 2 * 1 := rfl
          _ = 2 * (xs.length + 1) :=
            (Nat.mul_add _ _ _).symm

/-- Complete shared-DAG update allocation trace, including the final sum node. -/
def sharedUpdateEvents (v : Nat) (e : Expr) : List SharedAllocationEvent :=
  sharedPairEvents (dagDependentNodes v e) ++ [.finalAdd]

/-- Observable allocation count of the structurally hash-consed memo evaluator. -/
def sharedAllocated : AllocationCount :=
  fun v e => (sharedUpdateEvents v e).length

/-- Exact shared-DAG budget realized by the executable allocation trace. -/
def sharedDAGUpdateBudget (v : Nat) (e : Expr) : Nat :=
  1 + 2 * dagDependentCount v e

/-- The shared allocator realizes its DAG budget with equality. -/
theorem sharedAllocated_eq_dagBudget (v : Nat) (e : Expr) :
    sharedAllocated v e = sharedDAGUpdateBudget v e := by
  simp [sharedAllocated, sharedUpdateEvents, sharedDAGUpdateBudget,
    dagDependentCount, sharedPairEvents_length, Nat.add_comm]

/-- Hash-consing can only improve on the tree-shaped concrete reference
allocator's allocation count. -/
theorem sharedAllocated_le_referenceAllocated (v : Nat) (e : Expr) :
    sharedAllocated v e ≤ referenceAllocated v e := by
  rw [sharedAllocated_eq_dagBudget, referenceAllocated_eq_budget]
  unfold sharedDAGUpdateBudget supportSensitiveUpdateBudget
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 (dagDependentCount_le_dependentConeSize v e)) 1

/-- If the eliminated variable is absent, the shared evaluator allocates only
the final update node. -/
theorem sharedAllocated_eq_one_of_free
    (v : Nat) (e : Expr) (hfree : FreeOf v e) :
    sharedAllocated v e = 1 := by
  have hzero : dependentConeSize v e = 0 :=
    dependentConeSize_eq_zero_of_free v e hfree
  have hocc : dependentOccurrenceNodes v e = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [dependentOccurrenceNodes_length]
    exact hzero
  simp [sharedAllocated, sharedUpdateEvents, dagDependentNodes,
    dedupNodes, hocc, sharedPairEvents]

/-- Regression witness with genuine sharing. `s` appears twice syntactically,
but structural hash-consing allocates cofactors for it only once. -/
def repeatedDependentExample : Expr :=
  let s : Expr := .add (.var 0) (.const 7)
  .mul s s

/-- Tree-shaped support accounting sees five affected occurrences. -/
theorem repeatedDependentExample_treeCone :
    dependentConeSize 0 repeatedDependentExample = 5 := by
  decide

/-- Structural hash-consing collapses those five occurrences to three nodes. -/
theorem repeatedDependentExample_dagCone :
    dagDependentCount 0 repeatedDependentExample = 3 := by
  decide

/-- Consequently the shared trace allocates seven nodes versus eleven for the
non-memoized support-sensitive reference traversal. -/
theorem repeatedDependentExample_sharedAllocated :
    sharedAllocated 0 repeatedDependentExample = 7 := by
  decide

theorem repeatedDependentExample_referenceAllocated :
    referenceAllocated 0 repeatedDependentExample = 11 := by
  decide

#print axioms dependentOccurrenceNodes_length
#print axioms dedupNodes_length_le
#print axioms dagDependentCount_le_dependentConeSize
#print axioms sharedPairEvents_length
#print axioms sharedAllocated_eq_dagBudget
#print axioms sharedAllocated_le_referenceAllocated
#print axioms sharedAllocated_eq_one_of_free
#print axioms repeatedDependentExample_sharedAllocated

end DAGRestrictionUpdate
