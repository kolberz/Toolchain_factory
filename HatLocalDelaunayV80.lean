import Mathlib.Tactic

namespace HatV80

/-- Every interior edge in the current triangulation satisfies the exact local
Delaunay predicate. -/
def AllLocalLegal {Edge : Type}
    (interior legal : Edge → Prop) : Prop :=
  ∀ e, interior e → legal e

/-- Dynamic deletion seam: unchanged interior edges inherit legality; only
changed interior edges require a fresh exact local-Delaunay receipt. -/
theorem allLocalLegal_localUpdate {Edge : Type}
    (oldInterior newInterior oldLegal newLegal affected : Edge → Prop)
    (hold : AllLocalLegal oldInterior oldLegal)
    (hinterior : ∀ e, ¬ affected e → newInterior e → oldInterior e)
    (hlegal : ∀ e, ¬ affected e → oldLegal e → newLegal e)
    (hchanged : ∀ e, affected e → newInterior e → newLegal e) :
    AllLocalLegal newInterior newLegal := by
  intro e he
  by_cases ha : affected e
  · exact hchanged e ha he
  · exact hlegal e ha (hold e (hinterior e ha he))

/-- Iterated local-legality inheritance along the deletion chain. -/
theorem allLocalLegal_chain {Edge : Type}
    (interior legal affected : Nat → Edge → Prop)
    (h0 : AllLocalLegal (interior 0) (legal 0))
    (hinterior : ∀ n e, ¬ affected n e → interior (n+1) e → interior n e)
    (hlegal : ∀ n e, ¬ affected n e → legal n e → legal (n+1) e)
    (hchanged : ∀ n e, affected n e → interior (n+1) e → legal (n+1) e) :
    ∀ n, AllLocalLegal (interior n) (legal n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact allLocalLegal_localUpdate
        (interior n) (interior (n+1))
        (legal n) (legal (n+1))
        (affected n) ih
        (fun e ha he => hinterior n e ha he)
        (fun e ha hl => hlegal n e ha hl)
        (fun e ha he => hchanged n e ha he)


structure ZPoint where
  x : ℤ
  y : ℤ

def zOrient (p q r : ZPoint) : ℤ :=
  (q.x-p.x)*(r.y-p.y) - (q.y-p.y)*(r.x-p.x)

def zSqnorm (x y : ℤ) : ℤ := x*x + y*y

def zIncircle (p q r v : ZPoint) : ℤ :=
  let px := p.x-v.x
  let py := p.y-v.y
  let qx := q.x-v.x
  let qy := q.y-v.y
  let rx := r.x-v.x
  let ry := r.y-v.y
  zSqnorm px py * (qx*ry-qy*rx)
    - zSqnorm qx qy * (px*ry-py*rx)
    + zSqnorm rx ry * (px*qy-py*qx)

theorem incircle_edge_relation (p q r s v : ZPoint) :
    zIncircle p q r v * zOrient p q s
      - zIncircle p q r s * zOrient p q v
    = zIncircle p q s v * zOrient p q r := by
  unfold zIncircle zSqnorm zOrient
  ring

theorem zOrient_swap (p q r : ZPoint) :
    zOrient q p r = - zOrient p q r := by
  unfold zOrient
  ring

theorem zIncircle_swapEdge (p q r v : ZPoint) :
    zIncircle q p r v = - zIncircle p q r v := by
  unfold zIncircle zSqnorm
  ring

def potential (p q r v : ZPoint) : ℚ :=
  (zIncircle p q r v : ℚ) / (zOrient p q r : ℚ)

theorem potential_strictly_increases
    (p q r s v : ZPoint)
    (hr : 0 < zOrient p q r)
    (hs : zOrient p q s < 0)
    (hv : zOrient p q v < 0)
    (hstrict : zIncircle p q r s < 0) :
    potential p q r v < potential q p s v := by
  have hrel := incircle_edge_relation p q r s v
  have hprod : 0 < zIncircle p q r s * zOrient p q v :=
    mul_pos_of_neg_of_neg hstrict hv
  have hcross :
      zIncircle p q r v * (- zOrient p q s)
        < (- zIncircle p q s v) * zOrient p q r := by
    nlinarith
  have hrq : (0 : ℚ) < (zOrient p q r : ℚ) := by exact_mod_cast hr
  have hsqZ : 0 < - zOrient p q s := by omega
  have hsq : (0 : ℚ) < ((- zOrient p q s : ℤ) : ℚ) := by exact_mod_cast hsqZ
  unfold potential
  have hI : zIncircle q p s v = - zIncircle p q s v := zIncircle_swapEdge p q s v
  have hO : zOrient q p s = - zOrient p q s := zOrient_swap p q s
  rw [hI, hO]
  simp only [Int.cast_neg]
  apply (div_lt_div_iff₀ hrq hsq).2
  exact_mod_cast hcross

structure Tri where
  a : ZPoint
  b : ZPoint
  c : ZPoint

def Incident (t : Tri) (v : ZPoint) : Prop :=
  v = t.a ∨ v = t.b ∨ v = t.c

def InsideClosed (t : Tri) (v : ZPoint) : Prop :=
  0 ≤ zOrient t.a t.b v ∧
  0 ≤ zOrient t.b t.c v ∧
  0 ≤ zOrient t.c t.a v

def triPotential (t : Tri) (v : ZPoint) : ℚ :=
  potential t.a t.b t.c v

def StrictNeighborToward (v : ZPoint) (t u : Tri) : Prop :=
  ∃ p q r s,
    triPotential t v = potential p q r v ∧
    u = ⟨q,p,s⟩ ∧
    0 < zOrient p q r ∧
    zOrient p q s < 0 ∧
    zOrient p q v < 0 ∧
    zIncircle p q r s < 0

theorem outside_has_negative_edge
    (t : Tri) (v : ZPoint)
    (hout : ¬ InsideClosed t v) :
    zOrient t.a t.b v < 0 ∨
    zOrient t.b t.c v < 0 ∨
    zOrient t.c t.a v < 0 := by
  unfold InsideClosed at hout
  omega

/-- Abstract seam supplied by the already-certified straight-line triangulation
state. Each nonboundary oriented edge of a CCW face has exactly one adjacent
face on its opposite side, and that shared edge is strictly locally Delaunay. -/
def InteriorEdgeWitness {Face : Type}
    (tri : Face → Tri)
    (boundary : ZPoint → ZPoint → Prop) : Prop :=
  (∀ f, ¬ boundary (tri f).a (tri f).b →
    ∃ g s, tri g = ⟨(tri f).b, (tri f).a, s⟩ ∧
      zOrient (tri f).a (tri f).b s < 0 ∧
      zIncircle (tri f).a (tri f).b (tri f).c s < 0) ∧
  (∀ f, ¬ boundary (tri f).b (tri f).c →
    ∃ g s, tri g = ⟨(tri f).c, (tri f).b, s⟩ ∧
      zOrient (tri f).b (tri f).c s < 0 ∧
      zIncircle (tri f).b (tri f).c (tri f).a s < 0) ∧
  (∀ f, ¬ boundary (tri f).c (tri f).a →
    ∃ g s, tri g = ⟨(tri f).a, (tri f).c, s⟩ ∧
      zOrient (tri f).c (tri f).a s < 0 ∧
      zIncircle (tri f).c (tri f).a (tri f).b s < 0)

theorem zOrient_cyclic1 (a b c : ZPoint) :
    zOrient b c a = zOrient a b c := by
  unfold zOrient
  ring

theorem zOrient_cyclic2 (a b c : ZPoint) :
    zOrient c a b = zOrient a b c := by
  unfold zOrient
  ring

theorem zIncircle_cyclic1 (a b c v : ZPoint) :
    zIncircle b c a v = zIncircle a b c v := by
  unfold zIncircle zSqnorm
  ring

theorem zIncircle_cyclic2 (a b c v : ZPoint) :
    zIncircle c a b v = zIncircle a b c v := by
  unfold zIncircle zSqnorm
  ring

theorem potential_cyclic1 (a b c v : ZPoint) :
    potential b c a v = potential a b c v := by
  unfold potential
  rw [zIncircle_cyclic1, zOrient_cyclic1]

theorem potential_cyclic2 (a b c v : ZPoint) :
    potential c a b v = potential a b c v := by
  unfold potential
  rw [zIncircle_cyclic2, zOrient_cyclic2]

/-- Boundary support excludes any active target from the negative side of a
CCW boundary edge. -/
def BoundarySupportsTarget
    (boundary : ZPoint → ZPoint → Prop) (v : ZPoint) : Prop :=
  ∀ p q, boundary p q → 0 ≤ zOrient p q v

/-- Build the strict higher-potential adjacent-face witness directly from the
point-set triangulation seams: no foreign vertex lies in a closed face,
boundary edges support every active target, and every nonboundary edge has a
strictly locally-Delaunay opposite-side neighbor. -/
theorem strictNeighborToward_of_triangulationSeams
    {Face : Type}
    (tri : Face → Tri)
    (boundary : ZPoint → ZPoint → Prop)
    (v : ZPoint)
    (hccw : ∀ f, 0 < zOrient (tri f).a (tri f).b (tri f).c)
    (hforeign : ∀ f, ¬ Incident (tri f) v → ¬ InsideClosed (tri f) v)
    (hboundary : BoundarySupportsTarget boundary v)
    (hinterior : InteriorEdgeWitness tri boundary) :
    ∀ f, ¬ Incident (tri f) v →
      ∃ g, StrictNeighborToward v (tri f) (tri g) := by
  rcases hinterior with ⟨hAB,hBC,hCA⟩
  intro f hn
  have hout := hforeign f hn
  rcases outside_has_negative_edge (tri f) v hout with hab | hbc | hca
  · have hnb : ¬ boundary (tri f).a (tri f).b := by
      intro hb
      have hs := hboundary (tri f).a (tri f).b hb
      omega
    obtain ⟨g,s,hg,hs,hstrict⟩ := hAB f hnb
    refine ⟨g, (tri f).a, (tri f).b, (tri f).c, s, rfl, hg, hccw f, hs, hab, hstrict⟩
  · have hnb : ¬ boundary (tri f).b (tri f).c := by
      intro hb
      have hs := hboundary (tri f).b (tri f).c hb
      omega
    obtain ⟨g,s,hg,hs,hstrict⟩ := hBC f hnb
    have hrot : 0 < zOrient (tri f).b (tri f).c (tri f).a := by
      rw [zOrient_cyclic1]
      exact hccw f
    refine ⟨g, (tri f).b, (tri f).c, (tri f).a, s, ?_, hg, hrot, hs, hbc, hstrict⟩
    unfold triPotential
    exact (potential_cyclic1 (tri f).a (tri f).b (tri f).c v).symm
  · have hnb : ¬ boundary (tri f).c (tri f).a := by
      intro hb
      have hs := hboundary (tri f).c (tri f).a hb
      omega
    obtain ⟨g,s,hg,hs,hstrict⟩ := hCA f hnb
    have hrot : 0 < zOrient (tri f).c (tri f).a (tri f).b := by
      rw [zOrient_cyclic2]
      exact hccw f
    refine ⟨g, (tri f).c, (tri f).a, (tri f).b, s, ?_, hg, hrot, hs, hca, hstrict⟩
    unfold triPotential
    exact (potential_cyclic2 (tri f).a (tri f).b (tri f).c v).symm

theorem potential_increases_of_strictNeighbor
    {v : ZPoint} {t u : Tri}
    (h : StrictNeighborToward v t u) :
    triPotential t v < triPotential u v := by
  rcases h with ⟨p,q,r,s,ht,hu,hr,hs,hv,hstrict⟩
  have hinc := potential_strictly_increases p q r s v hr hs hv hstrict
  rw [ht]
  subst u
  exact hinc

theorem zIncircle_eq_zero_of_incident
    (t : Tri) (v : ZPoint) (h : Incident t v) :
    zIncircle t.a t.b t.c v = 0 := by
  rcases h with h | h | h
  · subst v; simp [zIncircle, zSqnorm]
  · subst v; simp [zIncircle, zSqnorm]
  · subst v; simp [zIncircle, zSqnorm]

theorem potential_eq_zero_of_incident
    (t : Tri) (v : ZPoint) (h : Incident t v) :
    triPotential t v = 0 := by
  unfold triPotential potential
  rw [zIncircle_eq_zero_of_incident t v h]
  norm_num

theorem finite_ascent_zero_ceiling
    {Face : Type} [Fintype Face] [Nonempty Face]
    (pot : Face → ℚ) (terminal : Face → Prop)
    (hadvance : ∀ f, ¬ terminal f → ∃ g, pot f < pot g)
    (hzero : ∀ f, terminal f → pot f = 0) :
    ∀ f, pot f ≤ 0 := by
  classical
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset Face) pot Finset.univ_nonempty
  have hmterm : terminal m := by
    by_contra hn
    obtain ⟨g,hmg⟩ := hadvance m hn
    have hgm := hmax g (Finset.mem_univ g)
    exact (not_lt_of_ge hgm) hmg
  have hmzero := hzero m hmterm
  intro f
  have hfm := hmax f (Finset.mem_univ f)
  linarith

theorem incircle_nonpos_of_potential_nonpos
    (p q r v : ZPoint)
    (hccw : 0 < zOrient p q r)
    (hpot : potential p q r v ≤ 0) :
    zIncircle p q r v ≤ 0 := by
  by_contra hnot
  have hposZ : 0 < zIncircle p q r v := by omega
  have hnum : (0 : ℚ) < (zIncircle p q r v : ℚ) := by exact_mod_cast hposZ
  have hden : (0 : ℚ) < (zOrient p q r : ℚ) := by exact_mod_cast hccw
  have hq : 0 < potential p q r v := div_pos hnum hden
  linarith

/-- Full finite-face local-edge criterion at the exact interface supplied by the
v77-v79 certificate: point-set face validity, supporting boundary, legal
incidence/opposite-side adjacency, and strict local Delaunay legality imply the
ordinary global empty-circumcircle property for the target. -/
theorem localDelaunay_globalEmpty_from_triangulationSeams
    {Face : Type} [Fintype Face] [Nonempty Face]
    (tri : Face → Tri)
    (boundary : ZPoint → ZPoint → Prop)
    (v : ZPoint)
    (hccw : ∀ f, 0 < zOrient (tri f).a (tri f).b (tri f).c)
    (hforeign : ∀ f, ¬ Incident (tri f) v → ¬ InsideClosed (tri f) v)
    (hboundary : BoundarySupportsTarget boundary v)
    (hinterior : InteriorEdgeWitness tri boundary) :
    ∀ f, zIncircle (tri f).a (tri f).b (tri f).c v ≤ 0 := by
  have hadvance := strictNeighborToward_of_triangulationSeams
    tri boundary v hccw hforeign hboundary hinterior
  have hpot : ∀ f, triPotential (tri f) v ≤ 0 := by
    apply finite_ascent_zero_ceiling
      (pot := fun f => triPotential (tri f) v)
      (terminal := fun f => Incident (tri f) v)
    · intro f hn
      obtain ⟨g,hg⟩ := hadvance f hn
      exact ⟨g, potential_increases_of_strictNeighbor hg⟩
    · intro f hf
      exact potential_eq_zero_of_incident (tri f) v hf
  intro f
  exact incircle_nonpos_of_potential_nonpos
    (tri f).a (tri f).b (tri f).c v (hccw f) (hpot f)


/-- All-target form used by a finite state certificate. The `hforeign` premise
is exactly the point-set triangulation semantic: a vertex not incident to a
face is not contained in that closed triangular face. The remaining premises
are the v77 supporting-boundary and v78/v79 incidence/coherence/local-edge
seams. -/
theorem localDelaunay_globalEmpty_allTargets
    {Face Target : Type} [Fintype Face] [Nonempty Face]
    (tri : Face → Tri)
    (boundary : ZPoint → ZPoint → Prop)
    (coord : Target → ZPoint)
    (hccw : ∀ f, 0 < zOrient (tri f).a (tri f).b (tri f).c)
    (hforeign : ∀ x f, ¬ Incident (tri f) (coord x) →
      ¬ InsideClosed (tri f) (coord x))
    (hboundary : ∀ x, BoundarySupportsTarget boundary (coord x))
    (hinterior : InteriorEdgeWitness tri boundary) :
    ∀ x f, zIncircle (tri f).a (tri f).b (tri f).c (coord x) ≤ 0 := by
  intro x
  exact localDelaunay_globalEmpty_from_triangulationSeams
    tri boundary (coord x) hccw (hforeign x) (hboundary x) hinterior

#print axioms HatV80.allLocalLegal_localUpdate
#print axioms HatV80.allLocalLegal_chain
#print axioms HatV80.strictNeighborToward_of_triangulationSeams
#print axioms HatV80.finite_ascent_zero_ceiling
#print axioms HatV80.localDelaunay_globalEmpty_from_triangulationSeams
#print axioms HatV80.localDelaunay_globalEmpty_allTargets

end HatV80
