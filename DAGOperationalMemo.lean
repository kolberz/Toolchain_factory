import DAGSharedMemo

namespace DAGRestrictionUpdate

/-- One executable memo-table entry: a structural input node and its already
materialized pair of Boolean cofactors. -/
structure MemoEntry where
  key : Expr
  pair : Expr × Expr
  deriving Repr, DecidableEq

/-- Runtime state of the structural memo evaluator. `events` records only fresh
cofactor-node materializations; cache hits append no allocation events. -/
structure MemoState where
  entries : List MemoEntry
  events : List SharedAllocationEvent
  deriving Repr, DecidableEq

/-- Empty memo state. -/
def emptyMemoState : MemoState :=
  { entries := [], events := [] }

/-- Deterministic executable lookup by structural expression identity. -/
def lookupMemo (e : Expr) : List MemoEntry → Option (Expr × Expr)
  | [] => none
  | entry :: rest =>
      if entry.key = e then some entry.pair else lookupMemo e rest

/-- Insert a freshly materialized pair and record exactly two allocation events. -/
def insertMemoPair
    (e : Expr) (p : Expr × Expr) (s : MemoState) : MemoState :=
  { entries := { key := e, pair := p } :: s.entries,
    events := s.events ++ [.cofactorZero e, .cofactorOne e] }

/-- Operational support-sensitive paired cofactor evaluator with structural
memoization.

* support-free compounds are reused immediately;
* dependent nodes are looked up before recursive work;
* a cache miss recursively materializes children, stores the resulting pair,
  and emits exactly two fresh-node events;
* a cache hit returns the stored pair without recursion or allocation. -/
def memoPairBuild (v : Nat) : Expr → MemoState → (Expr × Expr) × MemoState
  | .const c, s =>
      ((.const c, .const c), s)
  | .var x, s =>
      if h : x = v then
        match lookupMemo (.var x) s.entries with
        | some p => (p, s)
        | none =>
            let p : Expr × Expr := (.const 0, .const 1)
            (p, insertMemoPair (.var x) p s)
      else
        ((.var x, .var x), s)
  | e@(.add a b), s =>
      if hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0 then
        ((e, e), s)
      else
        match lookupMemo e s.entries with
        | some p => (p, s)
        | none =>
            let ra := memoPairBuild v a s
            let rb := memoPairBuild v b ra.2
            let p : Expr × Expr :=
              (.add ra.1.1 rb.1.1, .add ra.1.2 rb.1.2)
            (p, insertMemoPair e p rb.2)
  | e@(.mul a b), s =>
      if hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0 then
        ((e, e), s)
      else
        match lookupMemo e s.entries with
        | some p => (p, s)
        | none =>
            let ra := memoPairBuild v a s
            let rb := memoPairBuild v b ra.2
            let p : Expr × Expr :=
              (.mul ra.1.1 rb.1.1, .mul ra.1.2 rb.1.2)
            (p, insertMemoPair e p rb.2)

/-- Complete memoized update result, including the final update node. -/
structure OperationalMemoBuild where
  expression : Expr
  state : MemoState
  events : List SharedAllocationEvent
  deriving Repr, DecidableEq

/-- Run the operational memo evaluator from an empty cache. -/
def operationalMemoUpdateBuild (v : Nat) (e : Expr) : OperationalMemoBuild :=
  let r := memoPairBuild v e emptyMemoState
  { expression := .add r.1.1 r.1.2,
    state := r.2,
    events := r.2.events ++ [.finalAdd] }

/-- Observable fresh-node count of the operational memo evaluator. -/
def operationalMemoAllocated : AllocationCount :=
  fun v e => (operationalMemoUpdateBuild v e).events.length

/-- Concrete regression: the repeated dependent subexpression is memoized once,
so only three dependent structural nodes enter the cache. -/
theorem repeatedDependentExample_operational_entries :
    (operationalMemoUpdateBuild 0 repeatedDependentExample).state.entries.length = 3 := by
  decide

/-- Concrete regression: the operational evaluator emits seven total allocation
events, matching the shared-DAG accounting layer. -/
theorem repeatedDependentExample_operational_allocated :
    operationalMemoAllocated 0 repeatedDependentExample = 7 := by
  decide

/-- Concrete semantic regression for the shared-subexpression witness. This is a
computed certificate only; the general semantic theorem is a separate proof
obligation. -/
theorem repeatedDependentExample_operational_expression :
    (operationalMemoUpdateBuild 0 repeatedDependentExample).expression =
      update 0 repeatedDependentExample := by
  decide

/-- On the sharing witness the operational runtime and abstract shared accounting
agree exactly. -/
theorem repeatedDependentExample_operational_matches_shared :
    operationalMemoAllocated 0 repeatedDependentExample =
      sharedAllocated 0 repeatedDependentExample := by
  decide

#print axioms repeatedDependentExample_operational_entries
#print axioms repeatedDependentExample_operational_allocated
#print axioms repeatedDependentExample_operational_expression
#print axioms repeatedDependentExample_operational_matches_shared

end DAGRestrictionUpdate
