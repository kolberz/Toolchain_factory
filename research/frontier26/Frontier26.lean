import Frontier25

namespace WTCF26
open WTC
open WTCF21
open WTCF22
open WTCF23
open WTCF25

/-- One canonical bitmap word per residue slot. -/
def bitmapWords (m : Nat) (s : WTCF25.ResidueState m) : List Nat :=
  (WTCF24.allFin m).map (fun r => if s r then 1 else 0)

/-- Canonical list of active residue indices. -/
def activeIndices (m : Nat) (s : WTCF25.ResidueState m) : List (Fin m) :=
  (WTCF24.allFin m).filter (fun r => s r)

private theorem foldl_count_eq_add_filter_length {α : Type}
    (p : α → Bool) (xs : List α) (n : Nat) :
    xs.foldl (fun k x => if p x then k + 1 else k) n =
      n + (xs.filter p).length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases h : p x <;> simp [List.foldl, h, ih, Nat.add_assoc] <;> omega

/-- The canonical active-index list has exactly the old active-count measure. -/
theorem activeIndices_length (m : Nat) (s : WTCF25.ResidueState m) :
    (activeIndices m s).length = WTCF24.activeCount m s := by
  unfold activeIndices WTCF24.activeCount
  have h := foldl_count_eq_add_filter_length (fun r : Fin m => s r)
    (WTCF24.allFin m) 0
  simpa using h.symm

/-- Each active-residue witness is emitted as two structural words: residue index + marker. -/
def activePayload {m : Nat} : List (Fin m) → List Nat
  | [] => []
  | r :: rs => r.val :: 1 :: activePayload rs

@[simp] theorem activePayload_length {m : Nat} (rs : List (Fin m)) :
    (activePayload rs).length = 2 * rs.length := by
  induction rs with
  | nil => simp [activePayload]
  | cons r rs ih =>
      simp [activePayload, ih, Nat.mul_succ]

@[simp] theorem bitmapWords_length (m : Nat) (s : WTCF25.ResidueState m) :
    (bitmapWords m s).length = m := by
  simp [bitmapWords]

/-- Canonical emitted residue evidence used for Frontier-26 structural-size calibration. -/
def emitResidueEvidence (m : Nat) (s : WTCF25.ResidueState m) : List Nat :=
  bitmapWords m s ++ activePayload (activeIndices m s)

/-- Kernel-visible structural word count of emitted residue evidence. -/
def emittedEvidenceWords (m : Nat) (s : WTCF25.ResidueState m) : Nat :=
  (emitResidueEvidence m s).length

/-- Frontier-26 calibration theorem: the Frontier-24/25 predicted cost is exactly the
    structural word count of the canonical emitted evidence representation. -/
theorem emittedEvidenceWords_eq_certificateCost (m : Nat)
    (s : WTCF25.ResidueState m) :
    emittedEvidenceWords m s = WTCF24.certificateCost m s := by
  simp [emittedEvidenceWords, emitResidueEvidence, WTCF24.certificateCost,
    activeIndices_length]

/-- Canonical evidence attached to a successful Frontier-25 WTC residue certificate. -/
def certificateEvidence {I : SubsetSumFW} (c : WTCF25.CostedWTCObstruction I) : List Nat :=
  emitResidueEvidence c.modulus
    (WTCF25.linearRun c.modulus c.positive (I.values.map wordValue))

/-- Exact structural word count of one successful certificate. -/
def certificateWords {I : SubsetSumFW} (c : WTCF25.CostedWTCObstruction I) : Nat :=
  (certificateEvidence c).length

/-- The stored predicted cost of every successful certificate exactly equals the emitted
    evidence word count. This is structural-unit calibration, not a byte-size claim. -/
theorem cost_eq_certificateWords {I : SubsetSumFW}
    (c : WTCF25.CostedWTCObstruction I) :
    c.cost = certificateWords c := by
  calc
    c.cost = WTCF24.certificateCost c.modulus
        (WTCF25.linearRun c.modulus c.positive (I.values.map wordValue)) := c.cost_eq
    _ = emittedEvidenceWords c.modulus
        (WTCF25.linearRun c.modulus c.positive (I.values.map wordValue)) :=
      (emittedEvidenceWords_eq_certificateCost _ _).symm
    _ = certificateWords c := rfl

/-- Search work counts one candidate attempt per declared modulus. -/
def modulusSearchWork (mods : List Nat) : Nat := mods.length

/-- Materialization work is kept separate from search attempts and certificate size. -/
def portfolioMaterializationWork (I : SubsetSumFW) : List Nat → Nat
  | [] => 0
  | m :: ms =>
      WTCF25.linearRunWork m (I.values.map wordValue) + portfolioMaterializationWork I ms

/-- Exact materialization-work identity over a modulus portfolio. -/
theorem portfolioMaterializationWork_exact (I : SubsetSumFW) (mods : List Nat) :
    portfolioMaterializationWork I mods = I.values.length * mods.sum := by
  induction mods with
  | nil => simp [portfolioMaterializationWork]
  | cons m ms ih =>
      simp [portfolioMaterializationWork, WTCF25.linearRunWork_exact, ih,
        Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Explicit separation of the three cost dimensions certified in Frontier 26. -/
structure CostLedger where
  searchAttempts : Nat
  materializationLookups : Nat
  emittedCertificateWords : Nat
  deriving DecidableEq, Repr

/-- Ledger for one chosen certificate over one searched portfolio. -/
def costLedger {I : SubsetSumFW} (mods : List Nat)
    (c : WTCF25.CostedWTCObstruction I) : CostLedger := {
  searchAttempts := modulusSearchWork mods
  materializationLookups := portfolioMaterializationWork I mods
  emittedCertificateWords := certificateWords c
}

/-- Calibrated score of one modulus, using exact emitted structural word count when positive. -/
def calibratedScore (I : SubsetSumFW) (m : Nat) : Nat :=
  if hm : 0 < m then
    emittedEvidenceWords m
      (WTCF25.linearRun m hm (I.values.map wordValue))
  else 0

/-- Positive calibrated scores are exactly the inherited certificate-cost expression. -/
theorem calibratedScore_eq_certificateCost (I : SubsetSumFW) {m : Nat} (hm : 0 < m) :
    calibratedScore I m = WTCF24.certificateCost m
      (WTCF25.linearRun m hm (I.values.map wordValue)) := by
  simp [calibratedScore, hm, emittedEvidenceWords_eq_certificateCost]

/-- Adaptive stable promotion pass: scores at or below `cutoff` are kept in front;
    scores above the cutoff are deferred to the tail. No modulus is dropped. -/
def adaptiveOrder (I : SubsetSumFW) (cutoff : Nat) : List Nat → List Nat
  | [] => []
  | m :: ms =>
      let rest := adaptiveOrder I cutoff ms
      if calibratedScore I m ≤ cutoff then m :: rest else rest ++ [m]

/-- Adaptive ordering preserves portfolio cardinality. -/
theorem adaptiveOrder_length (I : SubsetSumFW) (cutoff : Nat) (mods : List Nat) :
    (adaptiveOrder I cutoff mods).length = mods.length := by
  induction mods with
  | nil => simp [adaptiveOrder]
  | cons m ms ih =>
      simp only [adaptiveOrder]
      split <;> simp [ih]

/-- Adaptive ordering preserves the searched modulus set extensionally. -/
theorem mem_adaptiveOrder_iff (I : SubsetSumFW) (cutoff : Nat)
    (mods : List Nat) (m : Nat) :
    m ∈ adaptiveOrder I cutoff mods ↔ m ∈ mods := by
  induction mods with
  | nil => simp [adaptiveOrder]
  | cons a as ih =>
      simp only [adaptiveOrder]
      split <;> simp [ih, or_comm, or_left_comm, or_assoc]

/-- Search-attempt count is unchanged by adaptive ordering. -/
theorem adaptive_searchWork_preserved (I : SubsetSumFW) (cutoff : Nat)
    (mods : List Nat) :
    modulusSearchWork (adaptiveOrder I cutoff mods) = modulusSearchWork mods := by
  simp [modulusSearchWork, adaptiveOrder_length]

/-- A successful `tryCosted` result occurs in the collected-certificate list whenever its
    modulus occurs in the searched list. -/
theorem tryCosted_mem_collect {I : SubsetSumFW} {mods : List Nat}
    {m : Nat} {c : WTCF25.CostedWTCObstruction I}
    (hm : m ∈ mods) (ht : WTCF25.tryCosted I m = some c) :
    c ∈ WTCF25.collectCosted I mods := by
  induction mods generalizing m c with
  | nil => simp at hm
  | cons a as ih =>
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · simp [WTCF25.collectCosted, ht]
      · cases ha : WTCF25.tryCosted I a with
        | none =>
            simpa [WTCF25.collectCosted, ha] using ih hm ht
        | some d =>
            rw [WTCF25.collectCosted, ha]
            exact List.mem_cons_of_mem d (ih hm ht)

/-- Adaptive cost selector: reorder the same searched set, then apply the certified argmin. -/
def chooseAdaptiveCosted (I : SubsetSumFW) (cutoff : Nat) (mods : List Nat) :
    Option (WTCF25.CostedWTCObstruction I) :=
  WTCF25.chooseCosted I (adaptiveOrder I cutoff mods)

/-- Any adaptive residue certificate remains a sound exact source-UNSAT proof. -/
theorem chooseAdaptiveCosted_sound (I : SubsetSumFW) (cutoff : Nat) (mods : List Nat) :
    match chooseAdaptiveCosted I cutoff mods with
    | some c => ¬ ∃ base : Assignment, naturalSubsetAccepts I base
    | none => True := by
  cases h : chooseAdaptiveCosted I cutoff mods with
  | none => trivial
  | some c => exact WTCF25.no_source_witness_of_costed c

/-- Strong preservation theorem: adaptive selection is minimal against every successful
    candidate from the original pre-reordering searched portfolio. -/
theorem chooseAdaptiveCosted_minimal_original {I : SubsetSumFW} {cutoff : Nat}
    {mods : List Nat} {chosen : WTCF25.CostedWTCObstruction I}
    (hchoose : chooseAdaptiveCosted I cutoff mods = some chosen)
    {m : Nat} {c : WTCF25.CostedWTCObstruction I}
    (hm : m ∈ mods) (ht : WTCF25.tryCosted I m = some c) :
    chosen.cost ≤ c.cost := by
  have hchoose' : WTCF25.chooseCosted I (adaptiveOrder I cutoff mods) = some chosen := by
    simpa [chooseAdaptiveCosted] using hchoose
  apply WTCF25.chooseCosted_minimal hchoose'
  apply tryCosted_mem_collect
  · exact (mem_adaptiveOrder_iff I cutoff mods m).2 hm
  · exact ht

/-- The argmin guarantee transfers from predicted cost to exact emitted evidence words. -/
theorem chooseAdaptiveCosted_emitted_minimal {I : SubsetSumFW} {cutoff : Nat}
    {mods : List Nat} {chosen : WTCF25.CostedWTCObstruction I}
    (hchoose : chooseAdaptiveCosted I cutoff mods = some chosen)
    {m : Nat} {c : WTCF25.CostedWTCObstruction I}
    (hm : m ∈ mods) (ht : WTCF25.tryCosted I m = some c) :
    certificateWords chosen ≤ certificateWords c := by
  rw [← cost_eq_certificateWords chosen, ← cost_eq_certificateWords c]
  exact chooseAdaptiveCosted_minimal_original hchoose hm ht

/-- First-success selector retained solely to exhibit the cost of a static search order. -/
def chooseFirstCosted (I : SubsetSumFW) : List Nat → Option (WTCF25.CostedWTCObstruction I)
  | [] => none
  | m :: ms =>
      match WTCF25.tryCosted I m with
      | some c => some c
      | none => chooseFirstCosted I ms

/-- Width-3 encoding of natural value 5. -/
abbrev word5w3 : Word := [true, false, true]

/-- Exact natural control corresponding to Frontier-24's `[1,5] -> 3` cost example. -/
def calibrationDemo : SubsetSumFW := {
  width := 3
  values := [WTCF23.word1w3, word5w3]
  target := WTCF23.word3w3
}

@[simp] theorem calibrationDemo_wf : calibrationDemo.WellFormed := by
  simp [calibrationDemo, SubsetSumFW.WellFormed, WTCF23.word1w3,
    word5w3, WTCF23.word3w3]

abbrev calibrationOrder : List Nat := WTCF23.residuePortfolioModuli
abbrev calibrationCutoff : Nat := 9

example : calibrationOrder = [2, 3, 4, 5] := by decide
example : calibratedScore calibrationDemo 4 = 10 := by decide
example : calibratedScore calibrationDemo 5 = 9 := by decide
example : adaptiveOrder calibrationDemo calibrationCutoff calibrationOrder = [2, 3, 5, 4] := by decide

/-- Counterexample required by Frontier 26: the static first-success order emits a
    10-word certificate at modulus 4, while calibrated adaptive ordering emits a
    strictly smaller 9-word certificate at modulus 5 on the same searched modulus set. -/
theorem calibrated_adaptive_strictly_better :
    (chooseFirstCosted calibrationDemo calibrationOrder).map
        (fun c => (c.modulus, certificateWords c)) = some (4, 10) ∧
    (chooseFirstCosted calibrationDemo
        (adaptiveOrder calibrationDemo calibrationCutoff calibrationOrder)).map
        (fun c => (c.modulus, certificateWords c)) = some (5, 9) ∧
    9 < 10 := by
  decide

/-- Adaptive three-way compiler. GCD remains first and LRAT remains the terminal fallback. -/
def chooseAdaptivePortfolio (I : SubsetSumFW) (cutoff : Nat) : WTCF25.PortfolioResult I :=
  match WTCF22.tryGCD I with
  | some c => .gcd c
  | none =>
      match chooseAdaptiveCosted I cutoff WTCF23.residuePortfolioModuli with
      | some c => .residue c
      | none => .lrat

/-- Every proof-producing branch of the adaptive three-way compiler remains source-sound. -/
theorem adaptivePortfolio_certificate_sound (I : SubsetSumFW) (cutoff : Nat) :
    match chooseAdaptivePortfolio I cutoff with
    | .gcd c => ¬ ∃ base : Assignment, naturalSubsetAccepts I base
    | .residue c => ¬ ∃ base : Assignment, naturalSubsetAccepts I base
    | .lrat => True := by
  unfold chooseAdaptivePortfolio
  cases hg : WTCF22.tryGCD I with
  | some c => exact WTCF21.no_source_witness_of_mod c
  | none =>
      cases hc : chooseAdaptiveCosted I cutoff WTCF23.residuePortfolioModuli with
      | none => trivial
      | some c => exact WTCF25.no_source_witness_of_costed c

/-- Branch-preservation probes for the historical three-way compiler. -/
def isResidue {I : SubsetSumFW} : WTCF25.PortfolioResult I → Bool
  | .residue _ => true
  | _ => false

def isLRAT {I : SubsetSumFW} : WTCF25.PortfolioResult I → Bool
  | .lrat => true
  | _ => false

example : WTCF25.PortfolioResult.tag (chooseAdaptivePortfolio WTCF22.nonPow2Demo 9) = .gcd 6 := by decide
example : isResidue (chooseAdaptivePortfolio WTCF23.residueUpgrade 9) = true := by decide
example : isLRAT (chooseAdaptivePortfolio WTCF23.residueFallback 9) = true := by decide

/-- Retained exact compiled-target residue theorem is unchanged. -/
theorem residueUpgrade_target_unsat_retained :
    ¬ ∃ a, SatCNF a
      (compileProgram (compileClosedSubset WTCF23.residueUpgrade).insts
        (compileClosedSubset WTCF23.residueUpgrade).output) :=
  WTCF25.residueUpgrade_target_unsat_native

/-- Retained LRAT fallback theorem is unchanged. -/
theorem residueFallback_target_unsat_retained :
    ¬ ∃ a, SatCNF a WTCF23.residueFallbackTarget :=
  WTCF25.residueFallback_target_unsat_native

#print axioms activeIndices_length
#print axioms emittedEvidenceWords_eq_certificateCost
#print axioms cost_eq_certificateWords
#print axioms portfolioMaterializationWork_exact
#print axioms mem_adaptiveOrder_iff
#print axioms adaptive_searchWork_preserved
#print axioms chooseAdaptiveCosted_sound
#print axioms chooseAdaptiveCosted_minimal_original
#print axioms chooseAdaptiveCosted_emitted_minimal
#print axioms calibrated_adaptive_strictly_better
#print axioms adaptivePortfolio_certificate_sound
#print axioms residueUpgrade_target_unsat_retained
#print axioms residueFallback_target_unsat_retained

end WTCF26
