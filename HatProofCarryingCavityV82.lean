import HatLocalDelaunayV80

namespace HatV82

open HatV80

/-- A proof-carrying deletion constructor partitions every affected post-state
interior edge into one of the two executable v82 receipt classes.

`earDiagonal` is discharged by a reused v71 exact empty-circle ear certificate.
`cavitySeam` is discharged by a one-shot exact seam predicate emitted during
construction.  `cover` is the crucial no-missing-receipt obligation. -/
structure ConstructionLegalityReceipts {Edge : Type}
    (affected newInterior newLegal : Edge → Prop) where
  earDiagonal : Edge → Prop
  cavitySeam : Edge → Prop
  cover :
    ∀ e, affected e → newInterior e → earDiagonal e ∨ cavitySeam e
  earDiagonal_sound :
    ∀ e, earDiagonal e → newLegal e
  cavitySeam_sound :
    ∀ e, cavitySeam e → newLegal e

/-- Receipt coverage plus class soundness supplies exactly the `hchanged`
premise required by the v80 local-update theorem. -/
theorem changedLegal_of_constructionReceipts {Edge : Type}
    {affected newInterior newLegal : Edge → Prop}
    (r : ConstructionLegalityReceipts affected newInterior newLegal) :
    ∀ e, affected e → newInterior e → newLegal e := by
  intro e ha hi
  rcases r.cover e ha hi with hd | hs
  · exact r.earDiagonal_sound e hd
  · exact r.cavitySeam_sound e hs

/-- One proof-carrying v82 deletion step kernel-composes directly into the
v80 `AllLocalLegal` invariant.  Unaffected edges inherit legality; affected
post-state interior edges are discharged only through constructor receipts. -/
theorem allLocalLegal_proofCarryingUpdate {Edge : Type}
    (oldInterior newInterior oldLegal newLegal affected : Edge → Prop)
    (hold : AllLocalLegal oldInterior oldLegal)
    (hinterior : ∀ e, ¬ affected e → newInterior e → oldInterior e)
    (hlegal : ∀ e, ¬ affected e → oldLegal e → newLegal e)
    (receipts :
      ConstructionLegalityReceipts affected newInterior newLegal) :
    AllLocalLegal newInterior newLegal := by
  exact allLocalLegal_localUpdate
    oldInterior newInterior oldLegal newLegal affected
    hold hinterior hlegal
    (changedLegal_of_constructionReceipts receipts)

/-- Iterated proof-carrying deletion chain.  The executable constructor may
emit a fresh receipt partition at each step; no changed-edge legality rescan is
needed by the abstract acceptance composition. -/
theorem allLocalLegal_proofCarryingChain {Edge : Type}
    (interior legal affected : Nat → Edge → Prop)
    (h0 : AllLocalLegal (interior 0) (legal 0))
    (hinterior :
      ∀ n e, ¬ affected n e → interior (n + 1) e → interior n e)
    (hlegal :
      ∀ n e, ¬ affected n e → legal n e → legal (n + 1) e)
    (receipts :
      ∀ n, ConstructionLegalityReceipts
        (affected n) (interior (n + 1)) (legal (n + 1))) :
    ∀ n, AllLocalLegal (interior n) (legal n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact allLocalLegal_proofCarryingUpdate
        (interior n) (interior (n + 1))
        (legal n) (legal (n + 1))
        (affected n) ih
        (fun e ha hi => hinterior n e ha hi)
        (fun e ha hl => hlegal n e ha hl)
        (receipts n)

/-- If an affected post-state interior edge is not represented by either
receipt class, then the v82 coverage premise is impossible.  This makes the
missing-receipt falsification boundary explicit in the formal interface. -/
theorem missing_changed_edge_contradicts_receipt_coverage {Edge : Type}
    {affected newInterior newLegal : Edge → Prop}
    (r : ConstructionLegalityReceipts affected newInterior newLegal)
    (e : Edge)
    (ha : affected e)
    (hi : newInterior e)
    (hnoEar : ¬ r.earDiagonal e)
    (hnoSeam : ¬ r.cavitySeam e) :
    False := by
  rcases r.cover e ha hi with hd | hs
  · exact hnoEar hd
  · exact hnoSeam hs

#print axioms HatV82.changedLegal_of_constructionReceipts
#print axioms HatV82.allLocalLegal_proofCarryingUpdate
#print axioms HatV82.allLocalLegal_proofCarryingChain
#print axioms HatV82.missing_changed_edge_contradicts_receipt_coverage

end HatV82
