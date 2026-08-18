import Frontier24
import ResidueFallbackLRATBridge
import GCDExamples

namespace WTCF25
open WTC
open WTCF21
open WTCF22
open WTCF23

/-- The exact fixed-size state reused from Frontier 24. -/
abbrev ResidueState (m : Nat) := WTCF24.ResidueState m

/-- Turn a natural residue into its canonical `Fin m` representative. -/
def shiftFin (m : Nat) (hm : 0 < m) (v : Nat) : Fin m :=
  ⟨v % m, Nat.mod_lt _ hm⟩

/-- Direct predecessor lookup. Unlike Frontier 24, this transition performs one predecessor
    lookup per destination residue rather than scanning all `m` predecessor slots. -/
def linearStep (m : Nat) (hm : 0 < m) (v : Nat) (s : ResidueState m) : ResidueState m :=
  fun r => s r || s (r - shiftFin m hm v)

/-- Direct linear residue automaton. -/
def linearRun (m : Nat) (hm : 0 < m) : List Nat → ResidueState m
  | [] => WTCF24.initialState m
  | v :: vs => linearStep m hm v (linearRun m hm vs)

private theorem fin_sub_add_cancel {m : Nat} (hm : 0 < m) (r a : Fin m) :
    (r - a) + a = r := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  grind

private theorem fin_add_sub_cancel {m : Nat} (hm : 0 < m) (r a : Fin m) :
    (r + a) - a = r := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  grind

private theorem val_add_shift {m : Nat} (hm : 0 < m) (v : Nat) (q : Fin m) :
    (q + shiftFin m hm v).val = (q.val + v) % m := by
  rw [Fin.val_add]
  simp [shiftFin, Nat.add_mod]

/-- One direct transition has exactly the same skip/take semantics as the quadratic
    predecessor-scanning transition. -/
theorem linearStep_true_iff {m v : Nat} (hm : 0 < m) (s : ResidueState m) (r : Fin m) :
    linearStep m hm v s r = true ↔
      s r = true ∨
        ∃ q : Fin m, s q = true ∧ (v + q.val) % m = r.val := by
  let a := shiftFin m hm v
  constructor
  · intro h
    have hor : s r = true ∨ s (r - a) = true := by
      simpa [linearStep, a] using h
    rcases hor with hr | hp
    · exact Or.inl hr
    · right
      refine ⟨r - a, hp, ?_⟩
      have hfin : (r - a) + a = r := fin_sub_add_cancel hm r a
      have hv : ((r - a).val + v) % m = ((r - a) + a).val := by
        simpa [Nat.add_comm] using (val_add_shift hm v (r - a)).symm
      calc
        (v + (r - a).val) % m = ((r - a).val + v) % m := by rw [Nat.add_comm]
        _ = ((r - a) + a).val := hv
        _ = r.val := congrArg Fin.val hfin
  · intro h
    have hor : s r = true ∨ s (r - a) = true := by
      rcases h with hr | ht
      · exact Or.inl hr
      · rcases ht with ⟨q, hq, hsum⟩
        right
        have hfin : q + a = r := by
          apply Fin.ext
          have hv := val_add_shift hm v q
          simpa [Nat.add_comm] using hv.trans hsum
        have hp : r - a = q := by
          rw [← hfin]
          exact fin_add_sub_cancel hm q a
        simpa [hp] using hq
    simpa [linearStep, a] using hor

/-- The direct automaton is exact for ordinary natural subset sums. -/
theorem linearRun_exact {m : Nat} (hm : 0 < m) (vals : List Nat) (r : Fin m) :
    linearRun m hm vals r = true ↔ WTCF24.ExactReachable m vals r := by
  induction vals generalizing r with
  | nil =>
      simpa [linearRun] using (WTCF24.indexedRun_exact hm ([] : List Nat) r)
  | cons v vs ih =>
      rw [linearRun, linearStep_true_iff hm]
      rw [WTCF24.exactReachable_cons hm]
      constructor
      · intro h
        rcases h with hskip | htake
        · exact Or.inl ((ih r).mp hskip)
        · rcases htake with ⟨q, hq, hstep⟩
          exact Or.inr ⟨q, (ih q).mp hq, hstep⟩
      · intro h
        rcases h with hskip | htake
        · exact Or.inl ((ih r).mpr hskip)
        · rcases htake with ⟨q, hq, hstep⟩
          exact Or.inr ⟨q, (ih q).mpr hq, hstep⟩

/-- One materialized direct transition performs exactly one predecessor lookup per state slot. -/
def linearTransitionWork (m : Nat) : Nat := m

/-- Declared materialization work for the direct automaton. -/
def linearRunWork (m : Nat) : List Nat → Nat
  | [] => 0
  | _ :: vs => linearRunWork m vs + linearTransitionWork m

/-- Frontier-25 work theorem: full materialization is exactly `n*m` under the declared lookup model. -/
theorem linearRunWork_exact (m : Nat) (vals : List Nat) :
    linearRunWork m vals = vals.length * m := by
  induction vals with
  | nil => simp [linearRunWork]
  | cons v vs ih =>
      simp [linearRunWork, linearTransitionWork, ih, Nat.succ_mul, Nat.add_comm]

/-- The fixed indexed state still has exactly `m` addressable positions. -/
theorem linearStateSlots_exact (m : Nat) : (WTCF24.allFin m).length = m :=
  WTCF24.allFin_length m

/-- Under equal source lengths, the Frontier-24 natural selected sum of `wordValue`s is
    definitionally equivalent to the historical WTC natural selected sum. -/
theorem selectedValue_wordValues {bits : List Bool} {vals : List Word}
    (hlen : bits.length = vals.length) :
    WTCF24.selectedValue bits (vals.map wordValue) = WTC.selectedValue bits vals := by
  induction bits generalizing vals with
  | nil =>
      cases vals <;> simp [WTCF24.selectedValue, WTC.selectedValue]
  | cons b bs ih =>
      cases vals with
      | nil => simp at hlen
      | cons v vs =>
          have hlen' : bs.length = vs.length := by simpa using hlen
          simp [WTCF24.selectedValue, WTC.selectedValue, ih hlen']

/-- Native WTC bridge: direct indexed-state truth is extensionally equivalent to the exact
    Frontier-23 list-residue relation. -/
theorem linearRun_iff_reachableResidues {m : Nat} (hm : 0 < m)
    (vals : List Word) (r : Fin m) :
    linearRun m hm (vals.map wordValue) r = true ↔
      r.val ∈ WTCF23.reachableResidues m vals := by
  rw [linearRun_exact hm]
  rw [WTCF23.mem_reachable_iff_exists_selectors]
  constructor
  · rintro ⟨bits, hlenMap, hsum⟩
    have hlen : bits.length = vals.length := by simpa using hlenMap
    have hsel := selectedValue_wordValues (bits := bits) (vals := vals) hlen
    rw [hsel] at hsum
    exact ⟨bits, hlen, hsum⟩
  · rintro ⟨bits, hlen, hsum⟩
    have hlenMap : bits.length = (vals.map wordValue).length := by simpa using hlen
    have hsel := selectedValue_wordValues (bits := bits) (vals := vals) hlen
    refine ⟨bits, hlenMap, ?_⟩
    rw [hsel]
    exact hsum

/-- Proof-carrying WTC residue certificate with an explicit predicted certificate cost. -/
structure CostedWTCObstruction (I : SubsetSumFW) where
  modulus : Nat
  positive : 0 < modulus
  targetAbsent :
    linearRun modulus positive (I.values.map wordValue)
      (WTCF24.targetFin modulus positive (wordValue I.target)) = false
  cost : Nat
  cost_eq : cost = WTCF24.certificateCost modulus
    (linearRun modulus positive (I.values.map wordValue))

/-- Construct a costed WTC certificate at one modulus. -/
def tryCosted (I : SubsetSumFW) (m : Nat) : Option (CostedWTCObstruction I) :=
  if hm : 0 < m then
    let idx := WTCF24.targetFin m hm (wordValue I.target)
    if h : linearRun m hm (I.values.map wordValue) idx = false then
      some {
        modulus := m
        positive := hm
        targetAbsent := h
        cost := WTCF24.certificateCost m (linearRun m hm (I.values.map wordValue))
        cost_eq := rfl
      }
    else none
  else none

/-- Convert a Frontier-25 cost certificate into the exact Frontier-23 semantic certificate. -/
def CostedWTCObstruction.toResidue {I : SubsetSumFW}
    (c : CostedWTCObstruction I) : WTCF23.ResidueObstruction I := {
  modulus := c.modulus
  modulusPos := c.positive
  targetAbsent := by
    intro hmem
    let idx := WTCF24.targetFin c.modulus c.positive (wordValue I.target)
    have h