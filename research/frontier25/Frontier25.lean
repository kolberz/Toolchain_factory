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
          have hsum' : (q.val + v) % m = r.val := by
            simpa [Nat.add_comm] using hsum
          exact hv.trans hsum'
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
      simpa [linearRun, WTCF24.indexedRun] using
        (WTCF24.indexedRun_exact hm ([] : List Nat) r)
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
    let idx : Fin c.modulus :=
      WTCF24.targetFin c.modulus c.positive (wordValue I.target)
    have hmemIdx : idx.val ∈ WTCF23.reachableResidues c.modulus I.values := by
      simpa [idx, WTCF24.targetFin] using hmem
    have hr : linearRun c.modulus c.positive (I.values.map wordValue) idx = true :=
      (linearRun_iff_reachableResidues c.positive I.values idx).mpr hmemIdx
    have hf : linearRun c.modulus c.positive (I.values.map wordValue) idx = false := by
      simpa [idx] using c.targetAbsent
    rw [hf] at hr
}

/-- Native WTC cost certificates prove exact source UNSAT. -/
theorem no_source_witness_of_costed {I : SubsetSumFW} (c : CostedWTCObstruction I) :
    ¬ ∃ base : Assignment, naturalSubsetAccepts I base :=
  WTCF23.no_source_witness_of_residue c.toResidue

/-- Native WTC cost certificates transport through the historical compiled-CNF bridge. -/
theorem target_unsat_of_costed {I : SubsetSumFW} (hI : I.WellFormed)
    (c : CostedWTCObstruction I) :
    ¬ ∃ a, SatCNF a (compileProgram (compileClosedSubset I).insts
      (compileClosedSubset I).output) :=
  WTCF23.target_unsat_of_residue hI c.toResidue

/-- Collect every successful costed residue proof in portfolio order. -/
def collectCosted (I : SubsetSumFW) : List Nat → List (CostedWTCObstruction I)
  | [] => []
  | m :: ms =>
      match tryCosted I m with
      | some c => c :: collectCosted I ms
      | none => collectCosted I ms

/-- Exact recursive minimum. Ties preserve earlier candidate order. -/
def minCosted {I : SubsetSumFW} : List (CostedWTCObstruction I) → Option (CostedWTCObstruction I)
  | [] => none
  | c :: cs =>
      match minCosted cs with
      | none => some c
      | some d => if c.cost ≤ d.cost then some c else some d

theorem minCosted_none_iff {I : SubsetSumFW} (cs : List (CostedWTCObstruction I)) :
    minCosted cs = none ↔ cs = [] := by
  cases cs with
  | nil => simp [minCosted]
  | cons c cs =>
      cases h : minCosted cs <;> simp [minCosted, h]

/-- The selected minimum is one of the input candidates. -/
theorem minCosted_mem {I : SubsetSumFW} {cs : List (CostedWTCObstruction I)}
    {chosen : CostedWTCObstruction I} (h : minCosted cs = some chosen) : chosen ∈ cs := by
  induction cs with
  | nil => simp [minCosted] at h
  | cons c cs ih =>
      cases hm : minCosted cs with
      | none =>
          have hnil : cs = [] := (minCosted_none_iff cs).mp hm
          subst cs
          simp [minCosted] at h
          simpa [h]
      | some d =>
          by_cases hcd : c.cost ≤ d.cost
          · simp [minCosted, hm, hcd] at h
            subst chosen
            simp
          · simp [minCosted, hm, hcd] at h
            subst chosen
            exact List.mem_cons_of_mem c (ih hm)

/-- Generic argmin theorem: the chosen certificate has cost no greater than every candidate. -/
theorem minCosted_minimal {I : SubsetSumFW} {cs : List (CostedWTCObstruction I)}
    {chosen : CostedWTCObstruction I} (h : minCosted cs = some chosen)
    {c : CostedWTCObstruction I} (hc : c ∈ cs) : chosen.cost ≤ c.cost := by
  induction cs with
  | nil => simp at hc
  | cons a as ih =>
      cases hm : minCosted as with
      | none =>
          have hnil : as = [] := (minCosted_none_iff as).mp hm
          subst as
          simp [minCosted] at h
          subst chosen
          simpa using hc
      | some d =>
          have hdm : ∀ {x : CostedWTCObstruction I}, x ∈ as → d.cost ≤ x.cost := by
            intro x hx
            exact ih hm hx
          by_cases had : a.cost ≤ d.cost
          · simp [minCosted, hm, had] at h
            subst chosen
            rcases List.mem_cons.mp hc with rfl | hc'
            · exact Nat.le_refl _
            · exact Nat.le_trans had (hdm hc')
          · simp [minCosted, hm, had] at h
            subst chosen
            rcases List.mem_cons.mp hc with rfl | hc'
            · exact Nat.le_of_lt (Nat.lt_of_not_ge had)
            · exact hdm hc'

/-- Cost-aware WTC selector. -/
def chooseCosted (I : SubsetSumFW) (mods : List Nat) : Option (CostedWTCObstruction I) :=
  minCosted (collectCosted I mods)

/-- Chosen cost is globally minimal over every successful candidate in the declared portfolio. -/
theorem chooseCosted_minimal {I : SubsetSumFW} {mods : List Nat}
    {chosen : CostedWTCObstruction I} (h : chooseCosted I mods = some chosen)
    {c : CostedWTCObstruction I} (hc : c ∈ collectCosted I mods) :
    chosen.cost ≤ c.cost :=
  minCosted_minimal h hc

/-- The chosen proof itself comes from the successful candidate set. -/
theorem chooseCosted_mem {I : SubsetSumFW} {mods : List Nat}
    {chosen : CostedWTCObstruction I} (h : chooseCosted I mods = some chosen) :
    chosen ∈ collectCosted I mods :=
  minCosted_mem h

inductive PortfolioResult (I : SubsetSumFW) where
  | gcd (cert : ModObstruction I)
  | residue (cert : CostedWTCObstruction I)
  | lrat

inductive PortfolioTag where
  | gcd (modulus : Nat)
  | residue (modulus : Nat)
  | lrat
  deriving DecidableEq, Repr

def PortfolioResult.tag {I : SubsetSumFW} : PortfolioResult I → PortfolioTag
  | .gcd c => .gcd c.modulus
  | .residue c => .residue c.modulus
  | .lrat => .lrat

/-- Exact Frontier-25 strategy order: inherited GCD, cost-aware direct residue, retained LRAT. -/
def choosePortfolio (I : SubsetSumFW) : PortfolioResult I :=
  match WTCF22.tryGCD I with
  | some c => .gcd c
  | none =>
      match chooseCosted I WTCF23.residuePortfolioModuli with
      | some c => .residue c
      | none => .lrat

/-- Every proof-producing Frontier-25 branch proves exact source UNSAT. -/
theorem portfolio_certificate_sound (I : SubsetSumFW) :
    match choosePortfolio I with
    | .gcd c => ¬ ∃ base : Assignment, naturalSubsetAccepts I base
    | .residue c => ¬ ∃ base : Assignment, naturalSubsetAccepts I base
    | .lrat => True := by
  unfold choosePortfolio
  cases hg : WTCF22.tryGCD I with
  | some c => exact WTCF21.no_source_witness_of_mod c
  | none =>
      cases hc : chooseCosted I WTCF23.residuePortfolioModuli with
      | none => trivial
      | some c => exact no_source_witness_of_costed c

/-- Retained GCD branch remains unchanged. -/
example : (choosePortfolio WTCF22.nonPow2Demo).tag = .gcd 6 := by decide

/-- Frontier-23 residue upgrade remains a residue proof and now uses the direct cost-aware state. -/
example : (choosePortfolio WTCF23.residueUpgrade).tag = .residue 3 := by decide

/-- Frontier-23 deliberately residue-inconclusive instance still falls through to LRAT. -/
example : (choosePortfolio WTCF23.residueFallback).tag = .lrat := by decide

/-- Direct cost certificate for the historical `[2,3] -> 1` upgrade. -/
def residueUpgradeCosted : CostedWTCObstruction WTCF23.residueUpgrade := by
  have h : (chooseCosted WTCF23.residueUpgrade WTCF23.residuePortfolioModuli).isSome = true := by decide
  exact (chooseCosted WTCF23.residueUpgrade WTCF23.residuePortfolioModuli).get
    (by simpa [Option.isSome_iff_ne_none] using h)

/-- The historical residue-upgrade source theorem now closes through the native direct state. -/
theorem residueUpgrade_no_source_witness_native :
    ¬ ∃ base : Assignment, naturalSubsetAccepts WTCF23.residueUpgrade base :=
  no_source_witness_of_costed residueUpgradeCosted

/-- The historical residue-upgrade compiled WTC target is UNSAT through the native direct state. -/
theorem residueUpgrade_target_unsat_native :
    ¬ ∃ a, SatCNF a
      (compileProgram (compileClosedSubset WTCF23.residueUpgrade).insts
        (compileClosedSubset WTCF23.residueUpgrade).output) :=
  target_unsat_of_costed WTCF21.fallbackDemo_wf residueUpgradeCosted

/-- The retained standard-LRAT fallback theorem is imported and remains the final obligation. -/
theorem residueFallback_target_unsat_native :
    ¬ ∃ a, SatCNF a WTCF23.residueFallbackTarget :=
  WTCF23.residue_fallback_target_unsat

/-- Full retained fallback closes source UNSAT after the costed residue selector declines it. -/
theorem residueFallback_native_closed :
    (choosePortfolio WTCF23.residueFallback).tag = .lrat ∧
    ¬ ∃ base : Assignment, naturalSubsetAccepts WTCF23.residueFallback base := by
  exact ⟨by decide, WTCF23.residue_fallback_no_source_witness⟩

#print axioms linearStep_true_iff
#print axioms linearRun_exact
#print axioms linearRunWork_exact
#print axioms selectedValue_wordValues
#print axioms linearRun_iff_reachableResidues
#print axioms target_unsat_of_costed
#print axioms chooseCosted_minimal
#print axioms portfolio_certificate_sound
#print axioms residueUpgrade_target_unsat_native
#print axioms residueFallback_target_unsat_native
#print axioms residueFallback_native_closed

end WTCF25
