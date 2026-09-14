import DAGOperationalMemo

namespace DAGRestrictionUpdate

/-- Every successful lookup in a valid memo table returns the specification-level
Boolean cofactor pair for that structural key. -/
def MemoValid (v : Nat) (entries : List MemoEntry) : Prop :=
  ∀ e p, lookupMemo e entries = some p → p = cofactorPair v e

/-- The empty cache is valid. -/
theorem emptyMemo_valid (v : Nat) :
    MemoValid v emptyMemoState.entries := by
  intro e p h
  simp [emptyMemoState, lookupMemo] at h

/-- Extending a valid table with a correct fresh pair preserves lookup validity. -/
theorem insertMemoPair_valid
    (v : Nat) (e : Expr) (p : Expr × Expr) (s : MemoState)
    (hs : MemoValid v s.entries)
    (hp : p = cofactorPair v e) :
    MemoValid v (insertMemoPair e p s).entries := by
  intro q r hlookup
  simp only [insertMemoPair, lookupMemo] at hlookup
  by_cases h : e = q
  · subst q
    simp at hlookup
    cases hlookup
    exact hp
  · simp [h] at hlookup
    exact hs q r hlookup

/-- Main operational invariant: starting from a valid memo table, the evaluator
returns the exact specification-level cofactor pair and leaves behind another
valid memo table. This makes cache hits semantically transparent. -/
theorem memoPairBuild_correct_valid
    (v : Nat) (e : Expr) (s : MemoState)
    (hs : MemoValid v s.entries) :
    (memoPairBuild v e s).1 = cofactorPair v e ∧
      MemoValid v (memoPairBuild v e s).2.entries := by
  induction e generalizing s with
  | const c =>
      simp [memoPairBuild, cofactorPair, hs]
  | var x =>
      by_cases hx : x = v
      · cases hlookup : lookupMemo (.var x) s.entries with
        | none =>
            have hins :
                MemoValid v
                  (insertMemoPair (.var x) (.const 0, .const 1) s).entries := by
              apply insertMemoPair_valid v (.var x) (.const 0, .const 1) s hs
              simp [cofactorPair, hx]
            simp [memoPairBuild, cofactorPair, hx, hlookup, hins]
        | some p =>
            have hp : p = cofactorPair v (.var x) := hs (.var x) p hlookup
            simp [memoPairBuild, hx, hlookup, hp, hs]
      · simp [memoPairBuild, cofactorPair, hx, hs]
  | add a b iha ihb =>
      by_cases hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · have ha : FreeOf v a :=
          (dependentConeSize_eq_zero_iff_free v a).1 hfree.1
        have hb : FreeOf v b :=
          (dependentConeSize_eq_zero_iff_free v b).1 hfree.2
        have hab : FreeOf v (.add a b) := ⟨ha, hb⟩
        have hself := cofactorPair_eq_self_of_free v (.add a b) hab
        simp [memoPairBuild, hfree, hself, hs]
      · cases hlookup : lookupMemo (.add a b) s.entries with
        | some p =>
            have hp : p = cofactorPair v (.add a b) :=
              hs (.add a b) p hlookup
            simp [memoPairBuild, hfree, hlookup, hp, hs]
        | none =>
            let ra := memoPairBuild v a s
            have ha := iha s hs
            have hraPair : ra.1 = cofactorPair v a := by
              simpa [ra] using ha.1
            have hraValid : MemoValid v ra.2.entries := by
              simpa [ra] using ha.2
            let rb := memoPairBuild v b ra.2
            have hb := ihb ra.2 hraValid
            have hrbPair : rb.1 = cofactorPair v b := by
              simpa [rb] using hb.1
            have hrbValid : MemoValid v rb.2.entries := by
              simpa [rb] using hb.2
            let p : Expr × Expr :=
              (.add ra.1.1 rb.1.1, .add ra.1.2 rb.1.2)
            have hp : p = cofactorPair v (.add a b) := by
              simp [p, cofactorPair, hraPair, hrbPair]
            have hins : MemoValid v (insertMemoPair (.add a b) p rb.2).entries :=
              insertMemoPair_valid v (.add a b) p rb.2 hrbValid hp
            simp [memoPairBuild, hfree, hlookup, ra, rb, p, hp, hins]
  | mul a b iha ihb =>
      by_cases hfree : dependentConeSize v a = 0 ∧ dependentConeSize v b = 0
      · have ha : FreeOf v a :=
          (dependentConeSize_eq_zero_iff_free v a).1 hfree.1
        have hb : FreeOf v b :=
          (dependentConeSize_eq_zero_iff_free v b).1 hfree.2
        have hab : FreeOf v (.mul a b) := ⟨ha, hb⟩
        have hself := cofactorPair_eq_self_of_free v (.mul a b) hab
        simp [memoPairBuild, hfree, hself, hs]
      · cases hlookup : lookupMemo (.mul a b) s.entries with
        | some p =>
            have hp : p = cofactorPair v (.mul a b) :=
              hs (.mul a b) p hlookup
            simp [memoPairBuild, hfree, hlookup, hp, hs]
        | none =>
            let ra := memoPairBuild v a s
            have ha := iha s hs
            have hraPair : ra.1 = cofactorPair v a := by
              simpa [ra] using ha.1
            have hraValid : MemoValid v ra.2.entries := by
              simpa [ra] using ha.2
            let rb := memoPairBuild v b ra.2
            have hb := ihb ra.2 hraValid
            have hrbPair : rb.1 = cofactorPair v b := by
              simpa [rb] using hb.1
            have hrbValid : MemoValid v rb.2.entries := by
              simpa [rb] using hb.2
            let p : Expr × Expr :=
              (.mul ra.1.1 rb.1.1, .mul ra.1.2 rb.1.2)
            have hp : p = cofactorPair v (.mul a b) := by
              simp [p, cofactorPair, hraPair, hrbPair]
            have hins : MemoValid v (insertMemoPair (.mul a b) p rb.2).entries :=
              insertMemoPair_valid v (.mul a b) p rb.2 hrbValid hp
            simp [memoPairBuild, hfree, hlookup, ra, rb, p, hp, hins]

/-- Running the operational cache from empty state returns exactly the paired
cofactor specification. -/
theorem memoPairBuild_correct (v : Nat) (e : Expr) :
    (memoPairBuild v e emptyMemoState).1 = cofactorPair v e := by
  exact (memoPairBuild_correct_valid v e emptyMemoState (emptyMemo_valid v)).1

/-- The actual memoized implementation computes the same update expression as
the original specification. -/
theorem operationalMemoUpdateBuild_expression (v : Nat) (e : Expr) :
    (operationalMemoUpdateBuild v e).expression = update v e := by
  have hp := memoPairBuild_correct v e
  simp [operationalMemoUpdateBuild, updateFromPair, updateFromPair_eq_update,
    hp]

/-- End-to-end semantic correctness of the operational structural memo evaluator. -/
theorem eval_operationalMemoUpdateBuild_eq_marginalize
    (ρ : Nat → Nat) (v : Nat) (e : Expr) :
    eval ρ (operationalMemoUpdateBuild v e).expression = marginalize ρ v e := by
  rw [operationalMemoUpdateBuild_expression]
  exact eval_update_eq_marginalize ρ v e

#print axioms emptyMemo_valid
#print axioms insertMemoPair_valid
#print axioms memoPairBuild_correct_valid
#print axioms memoPairBuild_correct
#print axioms operationalMemoUpdateBuild_expression
#print axioms eval_operationalMemoUpdateBuild_eq_marginalize

end DAGRestrictionUpdate
