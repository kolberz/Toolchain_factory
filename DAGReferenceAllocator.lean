import DAGCofactorPair
import DAGAllocatorContract

namespace DAGRestrictionUpdate

/-- Concrete allocation events emitted by the certified reference evaluator.
The two cofactor constructors are distinguished so the allocation count is the
length of an executable trace, rather than an assumed cost function. -/
inductive AllocationEvent where
  | varZero
  | varOne
  | addZero
  | addOne
  | mulZero
  | mulOne
  | finalAdd
  deriving Repr, DecidableEq

/-- Result of constructing both Boolean cofactors. `events` records every fresh
expression node allocated by this reference implementation. -/
structure ReferencePairBuild where
  zero : Expr
  one : Expr
  events : List AllocationEvent
  deriving Repr, DecidableEq

/-- Concrete support-sensitive cofactor allocator.

For a compound node, if both child dependent cones are empty, the original node
is reused for both cofactors and recursion stops at that node. Otherwise both
children are processed and exactly two fresh parent nodes are allocated. -/
def referencePairBuild (v : Nat) : Expr → ReferencePairBuild
  | .const c =>
      { zero := .const c, one := .const c, events := [] }
  | .var x =>
      if x = v then
        { zero := .const 0,
          one := .const 1,
          events := [.varZero, .varOne] }
      else
        { zero := .var x, one := .var x, events := [] }
  | .add a b =>
      if _h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0 then
        { zero := .add a b, one := .add a b, events := [] }
      else
        let ra := referencePairBuild v a
        let rb := referencePairBuild v b
        { zero := .add ra.zero rb.zero,
          one := .add ra.one rb.one,
          events := ra.events ++ rb.events ++ [.addZero, .addOne] }
  | .mul a b =>
      if _h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0 then
        { zero := .mul a b, one := .mul a b, events := [] }
      else
        let ra := referencePairBuild v a
        let rb := referencePairBuild v b
        { zero := .mul ra.zero rb.zero,
          one := .mul ra.one rb.one,
          events := ra.events ++ rb.events ++ [.mulZero, .mulOne] }

/-- The concrete allocator returns exactly the same two cofactors as the
specification-level paired traversal. -/
theorem referencePairBuild_pair (v : Nat) (e : Expr) :
    ((referencePairBuild v e).zero, (referencePairBuild v e).one) =
      cofactorPair v e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      by_cases h : x = v
      · simp [referencePairBuild, cofactorPair, h]
      · simp [referencePairBuild, cofactorPair, h]
  | add a b iha ihb =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · have ha : FreeOf v a :=
          (dependentConeSize_eq_zero_iff_free v a).1 h.1
        have hb : FreeOf v b :=
          (dependentConeSize_eq_zero_iff_free v b).1 h.2
        have hab : FreeOf v (.add a b) := by
          exact ⟨ha, hb⟩
        rw [cofactorPair_eq_self_of_free v (.add a b) hab]
        simp [referencePairBuild, h]
      · have ia0 :
            (referencePairBuild v a).zero = (cofactorPair v a).1 := by
          simpa using congrArg Prod.fst iha
        have ia1 :
            (referencePairBuild v a).one = (cofactorPair v a).2 := by
          simpa using congrArg Prod.snd iha
        have ib0 :
            (referencePairBuild v b).zero = (cofactorPair v b).1 := by
          simpa using congrArg Prod.fst ihb
        have ib1 :
            (referencePairBuild v b).one = (cofactorPair v b).2 := by
          simpa using congrArg Prod.snd ihb
        simp [referencePairBuild, cofactorPair, h, ia0, ia1, ib0, ib1]
  | mul a b iha ihb =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · have ha : FreeOf v a :=
          (dependentConeSize_eq_zero_iff_free v a).1 h.1
        have hb : FreeOf v b :=
          (dependentConeSize_eq_zero_iff_free v b).1 h.2
        have hab : FreeOf v (.mul a b) := by
          exact ⟨ha, hb⟩
        rw [cofactorPair_eq_self_of_free v (.mul a b) hab]
        simp [referencePairBuild, h]
      · have ia0 :
            (referencePairBuild v a).zero = (cofactorPair v a).1 := by
          simpa using congrArg Prod.fst iha
        have ia1 :
            (referencePairBuild v a).one = (cofactorPair v a).2 := by
          simpa using congrArg Prod.snd iha
        have ib0 :
            (referencePairBuild v b).zero = (cofactorPair v b).1 := by
          simpa using congrArg Prod.fst ihb
        have ib1 :
            (referencePairBuild v b).one = (cofactorPair v b).2 := by
          simpa using congrArg Prod.snd ihb
        simp [referencePairBuild, cofactorPair, h, ia0, ia1, ib0, ib1]

/-- The executable allocation-event count is exactly twice the dependent-cone
size: one fresh node for each cofactor at every affected syntax node. -/
theorem referencePairBuild_event_length (v : Nat) (e : Expr) :
    (referencePairBuild v e).events.length =
      2 * dependentConeSize v e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      by_cases h : x = v
      · simp [referencePairBuild, dependentConeSize, h]
      · simp [referencePairBuild, dependentConeSize, h]
  | add a b iha ihb =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simp [referencePairBuild, dependentConeSize, h]
      · simp [referencePairBuild, dependentConeSize, h, iha, ihb,
          Nat.mul_add, Nat.add_comm, Nat.add_left_comm]
  | mul a b iha ihb =>
      by_cases h : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simp [referencePairBuild, dependentConeSize, h]
      · simp [referencePairBuild, dependentConeSize, h, iha, ihb,
          Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

/-- Result of the complete update operation, including the final sum node. -/
structure ReferenceUpdateBuild where
  expression : Expr
  events : List AllocationEvent
  deriving Repr, DecidableEq

/-- Concrete update implementation built from the support-sensitive paired
cofactor allocator. -/
def referenceUpdateBuild (v : Nat) (e : Expr) : ReferenceUpdateBuild :=
  let r := referencePairBuild v e
  { expression := .add r.zero r.one,
    events := r.events ++ [.finalAdd] }

/-- The concrete implementation computes exactly the specification-level update. -/
theorem referenceUpdateBuild_expression (v : Nat) (e : Expr) :
    (referenceUpdateBuild v e).expression = update v e := by
  have hpair := referencePairBuild_pair v e
  rw [cofactorPair_eq_restrictions] at hpair
  have hzero := congrArg Prod.fst hpair
  have hone := congrArg Prod.snd hpair
  simp only at hzero hone
  simp [referenceUpdateBuild, update, hzero, hone]

/-- Observable allocation count exported to the allocator contract. -/
def referenceAllocated : AllocationCount :=
  fun v e => (referenceUpdateBuild v e).events.length

/-- Strong implementation theorem: the concrete event trace realizes the
support-sensitive budget with equality. -/
theorem referenceAllocated_eq_budget (v : Nat) (e : Expr) :
    referenceAllocated v e = supportSensitiveUpdateBudget v e := by
  simp [referenceAllocated, referenceUpdateBuild,
    referencePairBuild_event_length, supportSensitiveUpdateBudget,
    Nat.add_comm]

/-- The formerly abstract allocator-conformance premise is discharged by the
concrete executable reference implementation. -/
theorem reference_allocator_conforms :
    AllocatorConforms referenceAllocated := by
  intro v e
  exact Nat.le_of_eq (referenceAllocated_eq_budget v e)

/-- Exact implementation-level range avoidance. -/
theorem referenceAllocated_eq_one_of_free
    (v : Nat) (e : Expr) (hfree : FreeOf v e) :
    referenceAllocated v e = 1 := by
  rw [referenceAllocated_eq_budget]
  exact supportSensitiveUpdateBudget_eq_one_of_free v e hfree

/-- End-to-end semantic correctness of the concrete update evaluator. -/
theorem eval_referenceUpdateBuild_eq_marginalize
    (ρ : Nat → Nat) (v : Nat) (e : Expr) :
    eval ρ (referenceUpdateBuild v e).expression = marginalize ρ v e := by
  rw [referenceUpdateBuild_expression]
  exact eval_update_eq_marginalize ρ v e

#print axioms referencePairBuild_pair
#print axioms referencePairBuild_event_length
#print axioms referenceUpdateBuild_expression
#print axioms referenceAllocated_eq_budget
#print axioms reference_allocator_conforms
#print axioms referenceAllocated_eq_one_of_free
#print axioms eval_referenceUpdateBuild_eq_marginalize

end DAGRestrictionUpdate
