import Mathlib

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

namespace HatV53

/-- Deletion slice: all subsets of U of exact cardinality j. -/
def deletionSlice (U : Finset α) (j : ℕ) : Finset (Finset α) :=
  U.powersetLen j

@[simp]
theorem card_deletionSlice (U : Finset α) (j : ℕ) :
    (deletionSlice U j).card = Nat.choose U.card j := by
  simp [deletionSlice]

/-- State-dependent discrete derivative. -/
def discreteDeriv (L : Finset α → ℚ) (S : Finset α) (v : α) : ℚ :=
  L (insert v S) - L S

/-- Combinatorial incidence-count identity. -/
theorem card_pairs_nat (n j : ℕ) :
    (n - j) * Nat.choose n j = (j + 1) * Nat.choose n (j + 1) := by
  simpa [Nat.mul_comm] using (Nat.choose_succ_right_eq n j).symm

/-- Rational cast of the incidence-count identity, retaining truncated natural subtraction. -/
theorem card_pairs_eq_card_succ_slice (U : Finset α) (j : ℕ) :
    (((U.card - j : ℕ) : ℚ) * ((deletionSlice U j).card : ℚ)) =
      ((j + 1 : ℚ) * ((deletionSlice U (j + 1)).card : ℚ)) := by
  rw [card_deletionSlice, card_deletionSlice]
  exact_mod_cast card_pairs_nat U.card j

/-- Flat incidence universe for order j: (S,v) with |S|=j and v∈U\S. -/
def insertionPairs (U : Finset α) (j : ℕ) : Finset (Finset α × α) :=
  ((deletionSlice U j).product U).filter (fun p => p.2 ∉ p.1)

/-- Flat incidence universe for order j+1: (T,v) with |T|=j+1 and v∈T. -/
def succPairs (U : Finset α) (j : ℕ) : Finset (Finset α × α) :=
  ((deletionSlice U (j + 1)).product U).filter (fun p => p.2 ∈ p.1)

@[simp]
theorem mem_insertionPairs (U : Finset α) (j : ℕ) (p : Finset α × α) :
    p ∈ insertionPairs U j ↔ p.1 ∈ deletionSlice U j ∧ p.2 ∈ U \ p.1 := by
  simp [insertionPairs, and_assoc]

@[simp]
theorem mem_succPairs (U : Finset α) (j : ℕ) (p : Finset α × α) :
    p ∈ succPairs U j ↔ p.1 ∈ deletionSlice U (j + 1) ∧ p.2 ∈ p.1 := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpMem⟩
    rcases Finset.mem_product.mp hpProd with ⟨hT, _⟩
    exact ⟨hT, hpMem⟩
  · rintro ⟨hT, hv⟩
    have hTU : p.1 ⊆ U := (Finset.mem_powersetLen.mp hT).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hT, hTU hv⟩, hv⟩

/-- Recover a lower-slice set after inserting and deleting the distinguished vertex. -/
theorem insert_sdiff_cancel {S : Finset α} {v : α} (hv : v ∉ S) :
    (insert v S) \ {v} = S := by
  ext x
  simp [hv]

/-- Recover an upper-slice set after deleting and reinserting a member. -/
theorem sdiff_insert_cancel {T : Finset α} {v : α} (hv : v ∈ T) :
    insert v (T \ {v}) = T := by
  ext x
  by_cases hx : x = v
  · subst hx
    simp [hv]
  · simp [hx]

/-- Double-count insertion incidences by the lower or upper slice. -/
theorem sum_insertion_pairs_eq_slice_sum
    (U : Finset α) (L : Finset α → ℚ) (j : ℕ) (hj : j + 1 ≤ U.card) :
    (∑ S in deletionSlice U j, ∑ v in U \ S, L (insert v S)) =
      (j + 1 : ℚ) * (∑ T in deletionSlice U (j + 1), L T) := by
  have h_left :
      (∑ p in insertionPairs U j, L (insert p.2 p.1)) =
        ∑ S in deletionSlice U j, ∑ v in U \ S, L (insert v S) := by
    exact Finset.sum_finset_product
      (insertionPairs U j) (deletionSlice U j) (fun S => U \ S)
      (fun p => mem_insertionPairs U j p)

  have h_right :
      (∑ p in succPairs U j, L p.1) =
        ∑ T in deletionSlice U (j + 1), ∑ v in T, L T := by
    exact Finset.sum_finset_product
      (succPairs U j) (deletionSlice U (j + 1)) (fun T => T)
      (fun p => mem_succPairs U j p)

  have h_flat :
      (∑ p in insertionPairs U j, L (insert p.2 p.1)) =
        ∑ q in succPairs U j, L q.1 := by
    apply Finset.sum_bij'
      (fun p _ => (insert p.2 p.1, p.2))
      (fun q _ => (q.1 \ {q.2}, q.2))
    · intro p hp
      rw [mem_succPairs]
      rw [mem_insertionPairs] at hp
      rcases hp with ⟨hS, hv⟩
      have hvU : p.2 ∈ U := (Finset.mem_sdiff.mp hv).1
      have hvS : p.2 ∉ p.1 := (Finset.mem_sdiff.mp hv).2
      refine ⟨?_, Finset.mem_insert_self _ _⟩
      rw [deletionSlice, Finset.mem_powersetLen] at hS ⊢
      refine ⟨Finset.insert_subset hvU hS.1, ?_⟩
      rw [Finset.card_insert_of_not_mem hvS, hS.2]
    · intro q hq
      rw [mem_insertionPairs]
      rw [mem_succPairs] at hq
      rcases hq with ⟨hT, hvT⟩
      have hTU : q.1 ⊆ U := (Finset.mem_powersetLen.mp hT).1
      have hcardT : q.1.card = j + 1 := (Finset.mem_powersetLen.mp hT).2
      refine ⟨?_, ?_⟩
      · rw [deletionSlice, Finset.mem_powersetLen]
        refine ⟨Finset.Subset.trans (Finset.sdiff_subset q.1 {q.2}) hTU, ?_⟩
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hvT),
            Finset.card_singleton, hcardT]
        omega
      · rw [Finset.mem_sdiff]
        exact ⟨hTU hvT, by simp⟩
    · intro p hp
      rw [mem_insertionPairs] at hp
      have hvS : p.2 ∉ p.1 := (Finset.mem_sdiff.mp hp.2).2
      apply Prod.ext
      · exact insert_sdiff_cancel hvS
      · rfl
    · intro q hq
      rw [mem_succPairs] at hq
      apply Prod.ext
      · exact sdiff_insert_cancel hq.2
      · rfl
    · intro p hp
      rfl

  calc
    (∑ S in deletionSlice U j, ∑ v in U \ S, L (insert v S))
        = ∑ p in insertionPairs U j, L (insert p.2 p.1) := h_left.symm
    _ = ∑ q in succPairs U j, L q.1 := h_flat
    _ = ∑ T in deletionSlice U (j + 1), ∑ v in T, L T := h_right
    _ = (j + 1 : ℚ) * (∑ T in deletionSlice U (j + 1), L T) := by
      calc
        (∑ T in deletionSlice U (j + 1), ∑ _ in T, L T)
            = ∑ T in deletionSlice U (j + 1), ((T.card : ℚ) * L T) := by
                apply Finset.sum_congr rfl
                intro T hT
                rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ T in deletionSlice U (j + 1), ((j + 1 : ℚ) * L T) := by
              apply Finset.sum_congr rfl
              intro T hT
              have hcard : T.card = j + 1 := (Finset.mem_powersetLen.mp hT).2
              rw [hcard]
        _ = (j + 1 : ℚ) * (∑ T in deletionSlice U (j + 1), L T) := by
              rw [Finset.mul_sum]

/-- The loss term repeated over U\S has constant multiplicity |U|-j on the j-slice. -/
theorem sum_sdiff_const_loss
    (U : Finset α) (L : Finset α → ℚ) (j : ℕ) :
    (∑ S in deletionSlice U j, ∑ _ in U \ S, L S) =
      (((U.card - j : ℕ) : ℚ) * (∑ S in deletionSlice U j, L S)) := by
  have h_sdiff : ∀ S ∈ deletionSlice U j, (U \ S).card = U.card - j := by
    intro S hS
    have hSU : S ⊆ U := (Finset.mem_powersetLen.mp hS).1
    have hcard : S.card = j := (Finset.mem_powersetLen.mp hS).2
    rw [Finset.card_sdiff_of_subset hSU, hcard]
  calc
    (∑ S in deletionSlice U j, ∑ _ in U \ S, L S)
        = ∑ S in deletionSlice U j, (((U \ S).card : ℚ) * L S) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ S in deletionSlice U j, (((U.card - j : ℕ) : ℚ) * L S) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [h_sdiff S hS]
    _ = ((U.card - j : ℕ) : ℚ) * (∑ S in deletionSlice U j, L S) := by
          rw [Finset.mul_sum]

/-- Nonzero cardinality certificate for a nonempty combinatorial slice. -/
theorem card_deletionSlice_ne_zero (U : Finset α) (j : ℕ) (h : j ≤ U.card) :
    ((deletionSlice U j).card : ℚ) ≠ 0 := by
  rw [card_deletionSlice]
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos h))

/-- Nonzero natural-difference certificate after casting to ℚ. -/
theorem card_diff_ne_zero (U : Finset α) (j : ℕ) (h : j < U.card) :
    ((U.card - j : ℕ) : ℚ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.sub_pos_of_lt h))

/-- Normalized slice difference equals the uniform average of insertion derivatives. -/
theorem slice_average_diff_eq_pair_average
    (U : Finset α) (L : Finset α → ℚ) (j : ℕ) (hj : j + 1 ≤ U.card) :
    let A (k : ℕ) := (∑ S in deletionSlice U k, L S) / ((deletionSlice U k).card : ℚ)
    A (j + 1) - A j =
      (∑ S in deletionSlice U j, ∑ v in U \ S, discreteDeriv L S v) /
        (((deletionSlice U j).card : ℚ) * ((U.card - j : ℕ) : ℚ)) := by
  intro A
  have hj_lt : j < U.card := Nat.lt_of_succ_le hj
  have h_d1 : ((deletionSlice U j).card : ℚ) ≠ 0 :=
    card_deletionSlice_ne_zero U j (Nat.le_of_lt hj_lt)
  have h_d2 : ((deletionSlice U (j + 1)).card : ℚ) ≠ 0 :=
    card_deletionSlice_ne_zero U (j + 1) hj
  have h_d3 : ((U.card - j : ℕ) : ℚ) ≠ 0 := card_diff_ne_zero U j hj_lt
  have h_k : (j + 1 : ℚ) ≠ 0 := by positivity

  have h_deriv :
      (∑ S in deletionSlice U j, ∑ v in U \ S, discreteDeriv L S v) =
        (∑ S in deletionSlice U j, ∑ v in U \ S, L (insert v S)) -
        (∑ S in deletionSlice U j, ∑ v in U \ S, L S) := by
    simp [discreteDeriv, Finset.sum_sub_distrib]

  rw [h_deriv, sum_insertion_pairs_eq_slice_sum U L j hj,
      sum_sdiff_const_loss U L j]
  dsimp [A]

  let c1 : ℚ := ((deletionSlice U j).card : ℚ)
  let c2 : ℚ := ((deletionSlice U (j + 1)).card : ℚ)
  let d : ℚ := ((U.card - j : ℕ) : ℚ)
  let k : ℚ := (j + 1 : ℚ)
  let s1 : ℚ := ∑ S in deletionSlice U j, L S
  let s2 : ℚ := ∑ T in deletionSlice U (j + 1), L T

  have h_card : d * c1 = k * c2 := by
    simpa [c1, c2, d, k] using card_pairs_eq_card_succ_slice U j

  have h_top : (k * s2) / (c1 * d) = s2 / c2 := by
    rw [mul_comm c1 d, h_card]
    simpa using (mul_div_mul_left s2 c2 h_k)

  have h_bottom : (d * s1) / (c1 * d) = s1 / c1 := by
    rw [mul_comm c1 d]
    simpa using (mul_div_mul_left s1 c1 h_d3)

  change s2 / c2 - s1 / c1 = (k * s2 - d * s1) / (c1 * d)
  rw [sub_div, h_top, h_bottom]

#print axioms card_pairs_nat
#print axioms sum_insertion_pairs_eq_slice_sum
#print axioms sum_sdiff_const_loss
#print axioms slice_average_diff_eq_pair_average

end HatV53
