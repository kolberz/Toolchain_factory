import Mathlib.Tactic

namespace HatV80

/-- Abstract all-local-legality invariant for an interior-edge predicate. -/
def AllLocalLegal {Edge : Type}
    (interior legal : Edge → Prop) : Prop :=
  ∀ e, interior e → legal e

/-- Local update theorem: unaffected edges inherit old legality while affected
post-state interior edges are checked directly. -/
theorem allLocalLegal_localUpdate {Edge : Type}
    (oldInterior newInterior oldLegal newLegal affected : Edge → Prop)
    (hold : AllLocalLegal oldInterior oldLegal)
    (hinterior : ∀ e, ¬ affected e → newInterior e → oldInterior e)
    (hlegal : ∀ e, ¬ affected e → oldLegal e → newLegal e)
    (hchanged : ∀ e, affected e → newInterior e → newLegal e) :
    AllLocalLegal newInterior newLegal := by
  intro e hnew
  by_cases ha : affected e
  · exact hchanged e ha hnew
  · exact hlegal e ha (hold e (hinterior e ha hnew))

/-- Chain the local-update theorem over a sequence of states. -/
theorem allLocalLegal_chain {Edge : Type}
    (interior legal affected : Nat → Edge → Prop)
    (h0 : AllLocalLegal (interior 0) (legal 0))
    (hinterior :
      ∀ n e, ¬ affected n e → interior (n + 1) e → interior n e)
    (hlegal :
      ∀ n e, ¬ affected n e → legal n e → legal (n + 1) e)
    (hchanged :
      ∀ n e, affected n e → interior (n + 1) e → legal (n + 1) e) :
    ∀ n, AllLocalLegal (interior n) (legal n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact allLocalLegal_localUpdate
        (interior n) (interior (n + 1))
        (legal n) (legal (n + 1))
        (affected n) ih
        (fun e ha hi => hinterior n e ha hi)
        (fun e ha hl => hlegal n e ha hl)
        (fun e ha hi => hchanged n e ha hi)

/-- A normalized oriented incircle sign.  `orient = 1` stands for a positively
oriented triangle and `orient = -1` for a negatively oriented triangle. -/
def normalizedIncircle (orient raw : ℤ) : ℤ := orient * raw

/-- Strict local Delaunay legality is negative normalized incircle. -/
def StrictLocalLegal (orient raw : ℤ) : Prop :=
  normalizedIncircle orient raw < 0

/-- The normalized checker is invariant under simultaneously reversing the
triangle orientation and the raw determinant sign. -/
theorem normalizedIncircle_flip (orient raw : ℤ) :
    normalizedIncircle (-orient) (-raw) = normalizedIncircle orient raw := by
  simp [normalizedIncircle]
  ring

/-- Hence the strict local-legality proposition is orientation-normalized. -/
theorem strictLocalLegal_flip (orient raw : ℤ) :
    StrictLocalLegal (-orient) (-raw) ↔ StrictLocalLegal orient raw := by
  simp [StrictLocalLegal, normalizedIncircle_flip]

/-- Exact strict negativity excludes cocircularity. -/
theorem strictLocalLegal_raw_ne_zero
    (orient raw : ℤ) (h : StrictLocalLegal orient raw) : raw ≠ 0 := by
  intro hz
  subst raw
  simp [StrictLocalLegal, normalizedIncircle] at h

/-- Exact strict negativity also excludes degenerate orientation. -/
theorem strictLocalLegal_orient_ne_zero
    (orient raw : ℤ) (h : StrictLocalLegal orient raw) : orient ≠ 0 := by
  intro hz
  subst orient
  simp [StrictLocalLegal, normalizedIncircle] at h

/-- The executable local-edge check emits exact integer signs.  A negative
normalized sign is already a formal strict-local-legality witness. -/
theorem strictLocalLegal_of_normalized_negative
    (orient raw : ℤ) (h : normalizedIncircle orient raw < 0) :
    StrictLocalLegal orient raw := h

/-- Conversely the proposition exposes the exact integer inequality used by
execution. -/
theorem normalized_negative_of_strictLocalLegal
    (orient raw : ℤ) (h : StrictLocalLegal orient raw) :
    normalizedIncircle orient raw < 0 := h

/-- Boolean boundary for a strict normalized incircle test. -/
def strictLocalLegalB (orient raw : ℤ) : Bool :=
  decide (normalizedIncircle orient raw < 0)

@[simp]
theorem strictLocalLegalB_eq_true (orient raw : ℤ) :
    strictLocalLegalB orient raw = true ↔ StrictLocalLegal orient raw := by
  simp [strictLocalLegalB, StrictLocalLegal]

@[simp]
theorem strictLocalLegalB_eq_false (orient raw : ℤ) :
    strictLocalLegalB orient raw = false ↔ ¬ StrictLocalLegal orient raw := by
  simp [strictLocalLegalB, StrictLocalLegal]

/-- One strict local-Delaunay receipt. -/
structure LocalEdgeReceipt where
  orient : ℤ
  raw : ℤ
  accepted : Bool

/-- Receipt validity means the stored Boolean is exactly the strict exact
predicate; acceptance is not trusted independently of the determinant data. -/
def LocalEdgeReceipt.Valid (r : LocalEdgeReceipt) : Prop :=
  r.accepted = strictLocalLegalB r.orient r.raw

/-- Accepted valid receipts discharge the strict local-legality proposition. -/
theorem localEdgeReceipt_sound
    (r : LocalEdgeReceipt)
    (hv : r.Valid)
    (ha : r.accepted = true) :
    StrictLocalLegal r.orient r.raw := by
  rw [LocalEdgeReceipt.Valid] at hv
  rw [hv] at ha
  exact (strictLocalLegalB_eq_true r.orient r.raw).mp ha

/-- A rejected valid receipt refutes strict local legality. -/
theorem localEdgeReceipt_rejected
    (r : LocalEdgeReceipt)
    (hv : r.Valid)
    (ha : r.accepted = false) :
    ¬ StrictLocalLegal r.orient r.raw := by
  rw [LocalEdgeReceipt.Valid] at hv
  rw [hv] at ha
  exact (strictLocalLegalB_eq_false r.orient r.raw).mp ha

/-- Abstract finite bundle of local edge receipts. -/
structure LocalReceiptBundle (Edge : Type) where
  interior : Edge → Prop
  receipt : Edge → LocalEdgeReceipt
  receiptValid : ∀ e, interior e → (receipt e).Valid

/-- Every interior edge accepted by a valid bundle is formally strictly local
Delaunay. -/
theorem bundle_allLocalLegal_of_allAccepted {Edge : Type}
    (b : LocalReceiptBundle Edge)
    (hall : ∀ e, b.interior e → (b.receipt e).accepted = true) :
    AllLocalLegal b.interior
      (fun e => StrictLocalLegal (b.receipt e).orient (b.receipt e).raw) := by
  intro e hi
  exact localEdgeReceipt_sound (b.receipt e) (b.receiptValid e hi) (hall e hi)

/-- Edge-local legality can be transported across an unchanged edge when its
exact determinant pair is unchanged. -/
theorem strictLocalLegal_transport
    (oldOrient oldRaw newOrient newRaw : ℤ)
    (horient : oldOrient = newOrient)
    (hraw : oldRaw = newRaw)
    (h : StrictLocalLegal oldOrient oldRaw) :
    StrictLocalLegal newOrient newRaw := by
  simpa [horient, hraw] using h

/-- One-step exact local-Delaunay preservation theorem using exact integer
incircle data for changed post-state interior edges. -/
theorem exactLocalDelaunay_step {Edge : Type}
    (oldInterior newInterior affected : Edge → Prop)
    (oldOrient oldRaw newOrient newRaw : Edge → ℤ)
    (hold : AllLocalLegal oldInterior
      (fun e => StrictLocalLegal (oldOrient e) (oldRaw e)))
    (hinterior : ∀ e, ¬ affected e → newInterior e → oldInterior e)
    (horient : ∀ e, ¬ affected e → oldOrient e = newOrient e)
    (hraw : ∀ e, ¬ affected e → oldRaw e = newRaw e)
    (hchanged :
      ∀ e, affected e → newInterior e → normalizedIncircle (newOrient e) (newRaw e) < 0) :
    AllLocalLegal newInterior
      (fun e => StrictLocalLegal (newOrient e) (newRaw e)) := by
  exact allLocalLegal_localUpdate
    oldInterior newInterior
    (fun e => StrictLocalLegal (oldOrient e) (oldRaw e))
    (fun e => StrictLocalLegal (newOrient e) (newRaw e))
    affected hold hinterior
    (fun e ha hleg => strictLocalLegal_transport
      (oldOrient e) (oldRaw e) (newOrient e) (newRaw e)
      (horient e ha) (hraw e ha) hleg)
    (fun e ha hi => strictLocalLegal_of_normalized_negative
      (newOrient e) (newRaw e) (hchanged e ha hi))

/-- Full chain theorem for exact local-Delaunay preservation. -/
theorem exactLocalDelaunay_chain {Edge : Type}
    (interior affected : Nat → Edge → Prop)
    (orient raw : Nat → Edge → ℤ)
    (h0 : AllLocalLegal (interior 0)
      (fun e => StrictLocalLegal (orient 0 e) (raw 0 e)))
    (hinterior :
      ∀ n e, ¬ affected n e → interior (n + 1) e → interior n e)
    (horient :
      ∀ n e, ¬ affected n e → orient n e = orient (n + 1) e)
    (hraw :
      ∀ n e, ¬ affected n e → raw n e = raw (n + 1) e)
    (hchanged :
      ∀ n e, affected n e → interior (n + 1) e →
        normalizedIncircle (orient (n + 1) e) (raw (n + 1) e) < 0) :
    ∀ n, AllLocalLegal (interior n)
      (fun e => StrictLocalLegal (orient n e) (raw n e)) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact exactLocalDelaunay_step
        (interior n) (interior (n + 1)) (affected n)
        (orient n) (raw n) (orient (n + 1)) (raw (n + 1))
        ih
        (fun e ha hi => hinterior n e ha hi)
        (fun e ha => horient n e ha)
        (fun e ha => hraw n e ha)
        (fun e ha hi => hchanged n e ha hi)

/-- Changed-edge local checks suffice to preserve strict local Delaunay;
unchanged interior edges are inherited without a fresh incircle evaluation. -/
theorem changedEdgesSuffice {Edge : Type}
    (oldInterior newInterior affected : Edge → Prop)
    (oldOrient oldRaw newOrient newRaw : Edge → ℤ)
    (hold : AllLocalLegal oldInterior
      (fun e => StrictLocalLegal (oldOrient e) (oldRaw e)))
    (hinterior : ∀ e, ¬ affected e → newInterior e → oldInterior e)
    (horient : ∀ e, ¬ affected e → oldOrient e = newOrient e)
    (hraw : ∀ e, ¬ affected e → oldRaw e = newRaw e)
    (hchanged :
      ∀ e, affected e → newInterior e → strictLocalLegalB (newOrient e) (newRaw e) = true) :
    AllLocalLegal newInterior
      (fun e => StrictLocalLegal (newOrient e) (newRaw e)) := by
  exact exactLocalDelaunay_step
    oldInterior newInterior affected
    oldOrient oldRaw newOrient newRaw hold hinterior horient hraw
    (fun e ha hi =>
      normalized_negative_of_strictLocalLegal
        (newOrient e) (newRaw e)
        ((strictLocalLegalB_eq_true (newOrient e) (newRaw e)).mp
          (hchanged e ha hi)))

/-- If the changed-edge predicate is false for some affected post-state interior
edge, then a blanket `AllLocalLegal` claim is impossible.  This is the formal
falsification target used by the executable negative controls. -/
theorem changedEdgeFailure_refutes_allLocalLegal {Edge : Type}
    (newInterior affected : Edge → Prop)
    (newOrient newRaw : Edge → ℤ)
    (e : Edge)
    (ha : affected e)
    (hi : newInterior e)
    (hbad : ¬ StrictLocalLegal (newOrient e) (newRaw e)) :
    ¬ AllLocalLegal newInterior
      (fun x => StrictLocalLegal (newOrient x) (newRaw x)) := by
  intro hall
  exact hbad (hall e hi)

#check allLocalLegal_localUpdate
#check exactLocalDelaunay_step
#check exactLocalDelaunay_chain
#check changedEdgesSuffice
#check changedEdgeFailure_refutes_allLocalLegal

#print axioms allLocalLegal_localUpdate
#print axioms exactLocalDelaunay_step
#print axioms exactLocalDelaunay_chain
#print axioms changedEdgesSuffice
#print axioms changedEdgeFailure_refutes_allLocalLegal

end HatV80
