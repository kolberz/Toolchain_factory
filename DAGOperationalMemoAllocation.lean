import DAGOperationalMemo

namespace DAGRestrictionUpdate

/-- The operational memo state records exactly two allocation events per memo
entry. This invariant is independent of semantic correctness. -/
def MemoCountValid (s : MemoState) : Prop :=
  s.events.length = 2 * s.entries.length

/-- The empty runtime state satisfies the exact event/entry invariant. -/
theorem emptyMemo_count_valid : MemoCountValid emptyMemoState := by
  rfl

/-- Every cache insertion adds one memo entry and exactly two fresh-node events. -/
theorem insertMemoPair_count_valid
    (e : Expr) (p : Expr × Expr) (s : MemoState)
    (hs : MemoCountValid s) :
    MemoCountValid (insertMemoPair e p s) := by
  unfold MemoCountValid at hs ⊢
  simp [insertMemoPair, hs, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

/-- The recursive operational evaluator preserves the exact two-events-per-entry
runtime invariant. Cache hits and support-free reuse change neither side. -/
theorem memoPairBuild_count_valid
    (v : Nat) (e : Expr) (s : MemoState)
    (hs : MemoCountValid s) :
    MemoCountValid (memoPairBuild v e s).2 := by
  induction e generalizing s with
  | const c =>
      simpa [memoPairBuild] using hs
  | var x =>
      by_cases hx : x = v
      · subst x
        cases hlookup : lookupMemo (.var v) s.entries with
        | some p =>
            simpa [memoPairBuild, hlookup] using hs
        | none =>
            have hi := insertMemoPair_count_valid
              (.var v) (.const 0, .const 1) s hs
            simpa [memoPairBuild, hlookup] using hi
      · simpa [memoPairBuild, hx] using hs
  | add a b iha ihb =>
      by_cases hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simpa [memoPairBuild, hfree] using hs
      · cases hlookup : lookupMemo (.add a b) s.entries with
        | some p =>
            simpa [memoPairBuild, hfree, hlookup] using hs
        | none =>
            let ra := memoPairBuild v a s
            have hra : MemoCountValid ra.2 := by
              simpa [ra] using iha s hs
            let rb := memoPairBuild v b ra.2
            have hrb : MemoCountValid rb.2 := by
              simpa [rb] using ihb ra.2 hra
            let p : Expr × Expr :=
              (.add ra.1.1 rb.1.1, .add ra.1.2 rb.1.2)
            have hi := insertMemoPair_count_valid (.add a b) p rb.2 hrb
            simpa [memoPairBuild, hfree, hlookup, ra, rb, p] using hi
  | mul a b iha ihb =>
      by_cases hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simpa [memoPairBuild, hfree] using hs
      · cases hlookup : lookupMemo (.mul a b) s.entries with
        | some p =>
            simpa [memoPairBuild, hfree, hlookup] using hs
        | none =>
            let ra := memoPairBuild v a s
            have hra : MemoCountValid ra.2 := by
              simpa [ra] using iha s hs
            let rb := memoPairBuild v b ra.2
            have hrb : MemoCountValid rb.2 := by
              simpa [rb] using ihb ra.2 hra
            let p : Expr × Expr :=
              (.mul ra.1.1 rb.1.1, .mul ra.1.2 rb.1.2)
            have hi := insertMemoPair_count_valid (.mul a b) p rb.2 hrb
            simpa [memoPairBuild, hfree, hlookup, ra, rb, p] using hi

/-- Running from an empty cache leaves a state whose event count is exactly twice
its memo-entry count. -/
theorem operationalMemo_state_count_valid (v : Nat) (e : Expr) :
    MemoCountValid (operationalMemoUpdateBuild v e).state := by
  simpa [operationalMemoUpdateBuild] using
    memoPairBuild_count_valid v e emptyMemoState emptyMemo_count_valid

/-- Exact runtime accounting: total allocations are one final update node plus
two materialized cofactor nodes per cache entry. -/
theorem operationalMemoAllocated_eq_entries (v : Nat) (e : Expr) :
    operationalMemoAllocated v e =
      1 + 2 * (operationalMemoUpdateBuild v e).state.entries.length := by
  have hcount := operationalMemo_state_count_valid v e
  unfold MemoCountValid operationalMemoUpdateBuild at hcount
  simp [operationalMemoAllocated, operationalMemoUpdateBuild, hcount,
    Nat.add_comm]

/-- Processing an expression can append at most two allocation events for each
node in its tree-shaped dependent cone. Existing cache hits can only reduce this
amount. -/
theorem memoPairBuild_event_bound
    (v : Nat) (e : Expr) (s : MemoState) :
    (memoPairBuild v e s).2.events.length ≤
      s.events.length + 2 * dependentConeSize v e := by
  induction e generalizing s with
  | const c =>
      simp only [memoPairBuild, dependentConeSize, Nat.mul_zero, Nat.add_zero]
      exact Nat.le_refl _
  | var x =>
      by_cases hx : x = v
      · subst x
        cases hlookup : lookupMemo (.var v) s.entries with
        | some p =>
            simp only [memoPairBuild, if_pos rfl, dif_pos rfl, hlookup, dependentConeSize,
              Nat.mul_one]
            exact Nat.le_add_right _ _
        | none =>
            simp only [memoPairBuild, if_pos rfl, dif_pos rfl, hlookup, dependentConeSize,
              Nat.mul_one, insertMemoPair, List.length_append,
              List.length_cons, List.length_nil, Nat.add_zero]
            exact Nat.le_refl _
      · simp only [memoPairBuild, if_neg hx, dif_neg hx, dependentConeSize,
          Nat.mul_zero, Nat.add_zero]
        exact Nat.le_refl _
  | add a b iha ihb =>
      by_cases hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simp only [memoPairBuild, dependentConeSize, if_pos hfree, dif_pos hfree,
          Nat.mul_zero, Nat.add_zero]
        exact Nat.le_refl _
      · cases hlookup : lookupMemo (.add a b) s.entries with
        | some p =>
            simp only [memoPairBuild, dependentConeSize, if_neg hfree, dif_neg hfree, hlookup]
            exact Nat.le_add_right _ _
        | none =>
            let ra := memoPairBuild v a s
            have ha := iha s
            let rb := memoPairBuild v b ra.2
            have hb := ihb ra.2
            have hab := Nat.le_trans hb
              (Nat.add_le_add_right ha (2 * dependentConeSize v b))
            have htotal := Nat.add_le_add_right hab 2
            simpa only [memoPairBuild, dependentConeSize, if_neg hfree, dif_neg hfree, hlookup,
              insertMemoPair, ra, rb, List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Nat.mul_add, Nat.mul_one,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
  | mul a b iha ihb =>
      by_cases hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · simp only [memoPairBuild, dependentConeSize, if_pos hfree, dif_pos hfree,
          Nat.mul_zero, Nat.add_zero]
        exact Nat.le_refl _
      · cases hlookup : lookupMemo (.mul a b) s.entries with
        | some p =>
            simp only [memoPairBuild, dependentConeSize, if_neg hfree, dif_neg hfree, hlookup]
            exact Nat.le_add_right _ _
        | none =>
            let ra := memoPairBuild v a s
            have ha := iha s
            let rb := memoPairBuild v b ra.2
            have hb := ihb ra.2
            have hab := Nat.le_trans hb
              (Nat.add_le_add_right ha (2 * dependentConeSize v b))
            have htotal := Nat.add_le_add_right hab 2
            simpa only [memoPairBuild, dependentConeSize, if_neg hfree, dif_neg hfree, hlookup,
              insertMemoPair, ra, rb, List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Nat.mul_add, Nat.mul_one,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

/-- The actual operational memo evaluator never allocates more nodes than the
support-sensitive reference evaluator. -/
theorem operationalMemoAllocated_le_referenceAllocated
    (v : Nat) (e : Expr) :
    operationalMemoAllocated v e ≤ referenceAllocated v e := by
  have hbound := memoPairBuild_event_bound v e emptyMemoState
  rw [referenceAllocated_eq_budget]
  have htotal := Nat.add_le_add_right hbound 1
  simpa [operationalMemoAllocated, operationalMemoUpdateBuild,
    emptyMemoState, supportSensitiveUpdateBudget, Nat.add_comm] using htotal

/-- Therefore the real memoized evaluator discharges the allocator contract
without assuming a separate implementation-level cost premise. -/
theorem operationalMemo_allocator_conforms :
    AllocatorConforms operationalMemoAllocated := by
  intro v e
  rw [← referenceAllocated_eq_budget v e]
  exact operationalMemoAllocated_le_referenceAllocated v e

#print axioms emptyMemo_count_valid
#print axioms insertMemoPair_count_valid
#print axioms memoPairBuild_count_valid
#print axioms operationalMemo_state_count_valid
#print axioms operationalMemoAllocated_eq_entries
#print axioms memoPairBuild_event_bound
#print axioms operationalMemoAllocated_le_referenceAllocated
#print axioms operationalMemo_allocator_conforms

end DAGRestrictionUpdate
