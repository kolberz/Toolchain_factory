import HatSliceCalculusV53

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

namespace HatV53

set_option maxHeartbeats 0

/-- Uniform average of the absolute insertion derivative on the j-th slice. -/
def pairAbsAverage (U : Finset α) (L : Finset α → ℚ) (j : ℕ) : ℚ :=
  (∑ S ∈ deletionSlice U j, ∑ v ∈ U \ S, |discreteDeriv L S v|) /
    (((deletionSlice U j).card : ℚ) * ((U.card - j : ℕ) : ℚ))

/-- Triangle inequality for a finite rational sum, kept local to the v53 proof surface. -/
theorem abs_sum_le_sum_abs_finset {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → ℚ) :
    |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (abs_add_le _ _).trans (add_le_add (le_refl |f a|) ih)

/-- The absolute insertion-derivative sum is bounded by the sum of absolute derivatives. -/
theorem abs_insertion_deriv_sum_le_sum_abs
    (U : Finset α) (L : Finset α → ℚ) (j : ℕ) :
    |∑ S ∈ deletionSlice U j, ∑ v ∈ U \ S, discreteDeriv L S v| ≤
      ∑ S ∈ deletionSlice U j, ∑ v ∈ U \ S, |discreteDeriv L S v| := by
  calc
    |∑ S ∈ deletionSlice U j, ∑ v ∈ U \ S, discreteDeriv L S v|
        ≤ ∑ S ∈ deletionSlice U j,
            |∑ v ∈ U \ S, discreteDeriv L S v| :=
          abs_sum_le_sum_abs_finset (deletionSlice U j)
            (fun S => ∑ v ∈ U \ S, discreteDeriv L S v)
    _ ≤ ∑ S ∈ deletionSlice U j,
          ∑ v ∈ U \ S, |discreteDeriv L S v| := by
          exact Finset.sum_le_sum fun S hS =>
            abs_sum_le_sum_abs_finset (U \ S) (fun v => discreteDeriv L S v)

/-- One-step absolute slice movement is bounded by the pair-average absolute influence. -/
theorem slice_average_diff_abs_le_pairAbsAverage
    (U : Finset α) (L : Finset α → ℚ) (j : ℕ) (hj : j + 1 ≤ U.card) :
    let A (k : ℕ) :=
      (∑ S ∈ deletionSlice U k, L S) / ((deletionSlice U k).card : ℚ)
    |A (j + 1) - A j| ≤ pairAbsAverage U L j := by
  intro A
  have hj_lt : j < U.card := Nat.lt_of_succ_le hj
  have hcard_nat : 0 < (deletionSlice U j).card := by
    rw [card_deletionSlice]
    exact Nat.choose_pos (Nat.le_of_lt hj_lt)
  have hdiff_nat : 0 < U.card - j := Nat.sub_pos_of_lt hj_lt
  have hcard : 0 < ((deletionSlice U j).card : ℚ) := by exact_mod_cast hcard_nat
  have hdiff : 0 < ((U.card - j : ℕ) : ℚ) := by exact_mod_cast hdiff_nat
  have hden : 0 < ((deletionSlice U j).card : ℚ) * ((U.card - j : ℕ) : ℚ) :=
    mul_pos hcard hdiff

  have hstep := slice_average_diff_eq_pair_average U L j hj
  dsimp at hstep
  rw [hstep]
  rw [pairAbsAverage, abs_div, abs_of_pos hden]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (abs_insertion_deriv_sum_le_sum_abs U L j)
    (le_of_lt (inv_pos.mpr hden))

/-- Preregistered global v53 slice-influence bound.

It telescopes the certified one-step identity and applies the triangle inequality:
  |A_k - A_0| ≤ Σ_{j<k} E_{|S|=j,v∉S} |D_v L(S)|.
-/
theorem slice_average_global_bound
    (U : Finset α) (L : Finset α → ℚ) (k : ℕ) (hk : k ≤ U.card) :
    let A (m : ℕ) :=
      (∑ S ∈ deletionSlice U m, L S) / ((deletionSlice U m).card : ℚ)
    |A k - A 0| ≤ ∑ j ∈ Finset.range k, pairAbsAverage U L j := by
  intro A
  induction k with
  | zero => simp
  | succ k ih =>
      have hk_step : k + 1 ≤ U.card := by simpa [Nat.succ_eq_add_one] using hk
      have hk_prev : k ≤ U.card := Nat.le_trans (Nat.le_succ k) hk
      have hstep : |A (k + 1) - A k| ≤ pairAbsAverage U L k := by
        simpa [A] using slice_average_diff_abs_le_pairAbsAverage U L k hk_step
      have hprev : |A k - A 0| ≤ ∑ j ∈ Finset.range k, pairAbsAverage U L j :=
        ih hk_prev
      have hdecomp : A (k + 1) - A 0 = (A (k + 1) - A k) + (A k - A 0) := by
        ring
      rw [hdecomp]
      calc
        |(A (k + 1) - A k) + (A k - A 0)|
            ≤ |A (k + 1) - A k| + |A k - A 0| := abs_add_le _ _
        _ ≤ pairAbsAverage U L k +
              (∑ j ∈ Finset.range k, pairAbsAverage U L j) :=
            add_le_add hstep hprev
        _ = ∑ j ∈ Finset.range (k + 1), pairAbsAverage U L j := by
            rw [Finset.sum_range_succ]
            ring

#print axioms abs_sum_le_sum_abs_finset
#print axioms abs_insertion_deriv_sum_le_sum_abs
#print axioms slice_average_diff_abs_le_pairAbsAverage
#print axioms slice_average_global_bound

end HatV53
