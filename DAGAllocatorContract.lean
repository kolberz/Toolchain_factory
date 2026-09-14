import DAGSupportSensitive

namespace DAGRestrictionUpdate

/-- Abstract observable exported by a concrete hash-consed evaluator: the number
of nodes allocated while constructing the two cofactors and their final sum.
The concrete implementation supplies this function (or a trace that determines
it); the mathematics does not assume how the allocator is implemented. -/
abbrev AllocationCount := Nat → Expr → Nat

/-- Headline implementation boundary. A concrete DAG evaluator conforms when
its measured allocation count never exceeds the structural dependent-cone
budget proved in `DAGSupportSensitive`. -/
def AllocatorConforms (allocated : AllocationCount) : Prop :=
  ∀ v e, allocated v e ≤ supportSensitiveUpdateBudget v e

/-- A conforming allocator inherits the elementary whole-tree bound. -/
theorem allocation_le_tree_bound
    (allocated : AllocationCount)
    (hconf : AllocatorConforms allocated)
    (v : Nat) (e : Expr) :
    allocated v e ≤ 1 + 2 * treeSize e := by
  exact Nat.le_trans (hconf v e)
    (supportSensitiveUpdateBudget_le_treeBound v e)

/-- Range avoidance becomes an implementation-level allocation theorem once the
allocator discharges `AllocatorConforms`: eliminating a coordinate absent from
the subtree requires at most the final update node. -/
theorem allocation_le_one_of_free
    (allocated : AllocationCount)
    (hconf : AllocatorConforms allocated)
    (v : Nat) (e : Expr)
    (hfree : FreeOf v e) :
    allocated v e ≤ 1 := by
  have hbudget := hconf v e
  rw [supportSensitiveUpdateBudget_eq_one_of_free v e hfree] at hbudget
  exact hbudget

/-- If an implementation also reports that it allocated at least one node for
the final update constructor, range avoidance pins the count exactly to one. -/
theorem allocation_eq_one_of_free
    (allocated : AllocationCount)
    (hconf : AllocatorConforms allocated)
    (hfinal : ∀ v e, 1 ≤ allocated v e)
    (v : Nat) (e : Expr)
    (hfree : FreeOf v e) :
    allocated v e = 1 := by
  exact Nat.le_antisymm
    (allocation_le_one_of_free allocated hconf v e hfree)
    (hfinal v e)

/-- Per-run certificate shape for connecting an empirical allocator trace to the
formal bound without promoting the trace itself to an axiom. -/
structure AllocationReceipt where
  variable : Nat
  expression : Expr
  allocatedNodes : Nat
  budget : Nat
  budget_definition : budget = supportSensitiveUpdateBudget variable expression
  within_budget : allocatedNodes ≤ budget

/-- Every valid receipt yields the mathematical allocation bound for that run. -/
theorem receipt_allocation_bound (r : AllocationReceipt) :
    r.allocatedNodes ≤ supportSensitiveUpdateBudget r.variable r.expression := by
  rw [← r.budget_definition]
  exact r.within_budget

#print axioms allocation_le_tree_bound
#print axioms allocation_le_one_of_free
#print axioms allocation_eq_one_of_free
#print axioms receipt_allocation_bound

end DAGRestrictionUpdate
