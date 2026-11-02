import GlobalEmbedding.Paper.BalancedNativeChartGluingOnOpen
import GlobalEmbedding.Paper.HopfCollarSquarePairing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Compactness.Compact

/-!
# Compact gluing of actual native analytic collar germs

Source: `main.tex`, prop:collar, lines539–550. DAG: `collar-ck-compact-germ-gluing`.
W6 owns only this compact assembly. The actual geometric local CK construction and
same-initial-data joint germ uniqueness are supplied by W5, not reproved here.
All maps use the original whole Hopf product, original real time, and finite target.
-/

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {a N : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]

/-- Restrict an actual joint native analytic local collar to normal time at a fixed
sourcepoint. The tube is open, so native omega regularity gives actual real analyticity.
Source: the local analytic CK solutions in prop:collar, lines549–550. -/
theorem collarCK_local_time_analytic
    (U : Set (FreeHopfProduct C)) (hU : IsOpen U) (r : ℝ)
    (g : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω g (Ioo (-r) r ×ˢ U))
    (x : FreeHopfProduct C) (hx : x ∈ U) :
    AnalyticOnNhd ℝ (fun t ↦ g (t, x)) (Ioo (-r) r) := by
  intro t ht
  have ha : ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω g (t, x) :=
    hg.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨ht, hx⟩)
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (freeHopfModel C)) ω
      (fun s : ℝ ↦ (s, x)) := contMDiff_id.prodMk contMDiff_const
  exact (ha.comp t hc.contMDiffAt).contDiffAt.analyticAt

/-- Genuine joint CK germ agreement implies equality on the entire overlap of two
actual local tubes. Apply the vector-valued real analytic identity theorem on the
connected normal-time interval at each fixed sourcepoint. No uniform germ radius on
the possibly noncompact spatial overlap is needed. Source: prop:collar, lines549–550. -/
theorem collarCK_local_tubes_overlap
    (U W : Set (FreeHopfProduct C)) (hU : IsOpen U) (hW : IsOpen W)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (g h : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω g (Ioo (-r) r ×ˢ U))
    (hh : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω h (Ioo (-s) s ×ˢ W))
    (hjoint : ∀ x ∈ U, x ∈ W → g =ᶠ[𝓝 (0, x)] h) :
    EqOn g h ((Ioo (-r) r ×ˢ U) ∩ (Ioo (-s) s ×ˢ W)) := by
  rintro ⟨t, x⟩ ⟨⟨htr, hxU⟩, ⟨hts, hxW⟩⟩
  let J := Ioo (-(min r s)) (min r s)
  have hJr : J ⊆ Ioo (-r) r := by
    intro v hv
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left r s)) hv.1,
      lt_of_lt_of_le hv.2 (min_le_left r s)⟩
  have hJs : J ⊆ Ioo (-s) s := by
    intro v hv
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right r s)) hv.1,
      lt_of_lt_of_le hv.2 (min_le_right r s)⟩
  have hzero : (0 : ℝ) ∈ J := ⟨neg_neg_of_pos (lt_min hr hs), lt_min hr hs⟩
  have htJ : t ∈ J := by
    change -(min r s) < t ∧ t < min r s
    constructor
    · have hneg : -t < min r s := lt_min (by linarith [htr.1]) (by linarith [hts.1])
      linarith
    · exact lt_min htr.2 hts.2
  have hc : Tendsto (fun v : ℝ ↦ (v, x)) (𝓝 0) (𝓝 (0, x)) :=
    continuous_id.continuousAt.prodMk continuous_const.continuousAt
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    ((collarCK_local_time_analytic C U hU r g hg x hxU).mono hJr)
    ((collarCK_local_time_analytic C W hW s h hh x hxW).mono hJs)
    (convex_Ioo _ _).isPreconnected hzero ((hjoint x hxU hxW).comp_tendsto hc) htJ

/-- Actual native analytic tubes covering the whole initial Hopf product and genuine
pairwise joint germs glue to one actual jointly analytic collar on one positive common
interval. First extend each fixed-source time germ over the full interval overlap.
Reuse the accepted arbitrary-order open gluer at omega with identity partial charts on
the open union of the original tubes. Equality on each open tube gives JOINT germs.
The union contains zero times the compact whole source; ONE native tube lemma gives
the common positive interval. No selected global collar, overlap uniform radius, new
atlas, or smooth-to-analytic assertion is assumed. Source: prop:collar, lines549–550. -/
theorem collarCK_compact_germ_gluing {ι : Type*}
    (U : ι → Set (FreeHopfProduct C)) (hU : ∀ i, IsOpen (U i))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (g : ι → ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hcover : ∀ x, ∃ i, x ∈ U i)
    (hlocal : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω (g i) (Ioo (-(r i)) (r i) ×ˢ U i))
    (hjoint : ∀ i j x, x ∈ U i → x ∈ U j → g i =ᶠ[𝓝 (0, x)] g j) :
    ∃ δ > 0, ∃ G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
        𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω G (Ioo (-δ) δ ×ˢ univ) ∧
      (∀ z ∈ Ioo (-δ) δ ×ˢ (univ : Set (FreeHopfProduct C)),
        ∃ i, z ∈ Ioo (-(r i)) (r i) ×ˢ U i) ∧
      ∀ i z, z ∈ Ioo (-δ) δ ×ˢ (univ : Set (FreeHopfProduct C)) →
        z ∈ Ioo (-(r i)) (r i) ×ˢ U i → G =ᶠ[𝓝 z] g i := by
  let T (i : ι) := Ioo (-(r i)) (r i) ×ˢ U i
  have hT (i : ι) : IsOpen (T i) := isOpen_Ioo.prod (hU i)
  let D := ⋃ i, T i
  have hD : IsOpen D := isOpen_iUnion hT
  let e (i : ι) := OpenPartialHomeomorph.ofSet (T i) (hT i)
  have hc (z : ℝ × FreeHopfProduct C) (hz : z ∈ D) : ∃ i, z ∈ (e i).source :=
    mem_iUnion.mp hz
  have he (i : ι) : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      (𝓘(ℝ, ℝ).prod (freeHopfModel C)) ω (e i) (e i).source := contMDiffOn_id
  have hl (i : ι) : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω (g i) (e i).target := hlocal i
  have hij (i j : ι) (z : ℝ × FreeHopfProduct C) (_ : z ∈ D)
      (hi : z ∈ (e i).source) (hj : z ∈ (e j).source) : g i (e i z) = g j (e j z) :=
    collarCK_local_tubes_overlap C (U i) (U j) (hU i) (hU j) (r i) (r j)
      (hr i) (hr j) (g i) (g j) (hlocal i) (hlocal j) (hjoint i j) ⟨hi, hj⟩
  obtain ⟨G, hG, hGeq⟩ := balanced_native_chart_gluing_on_open
    (𝓘(ℝ, ℝ).prod (freeHopfModel C)) (𝓘(ℝ, ℝ).prod (freeHopfModel C))
    ω D hD e g hc he hl hij
  have hinitial : ({0} : Set ℝ) ×ˢ (univ : Set (FreeHopfProduct C)) ⊆ D := by
    rintro ⟨t, x⟩ ⟨ht, _⟩
    have ht0 : t = 0 := ht
    subst t
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, ⟨⟨neg_neg_of_pos (hr i), hr i⟩, hi⟩⟩
  obtain ⟨A, B, hA, _, h0A, hMB, hAB⟩ :=
    generalized_tube_lemma isCompact_singleton
      (isCompact_univ : IsCompact (univ : Set (FreeHopfProduct C))) hD hinitial
  have hzeroA : (0 : ℝ) ∈ A := h0A (by simp)
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hzeroA)
  have hsub : Ioo (-δ) δ ×ˢ (univ : Set (FreeHopfProduct C)) ⊆ D := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    apply hAB
    exact ⟨hδA (by simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using ht), hMB hx⟩
  refine ⟨δ, hδ, G, hG.mono hsub, fun z hz ↦ mem_iUnion.mp (hsub hz), ?_⟩
  intro i z _ hzi
  filter_upwards [(hT i).mem_nhds hzi] with y hy
  exact hGeq i y (mem_iUnion.mpr ⟨i, hy⟩) hy

omit [∀ i, Fact (0 < C i)] in
/-- Joint local equality preserves the actual normal derivative as a JOINT germ.
Pull each nearby germ back along the actual normal curve and use native derivative
congruence. No differentiability hypothesis is required for this locality fact.
Source: actual collar jets in prop:collar, lines539–550. -/
theorem collarCK_rDeriv_germ
    {f g : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)}
    {z : ℝ × FreeHopfProduct C} (hfg : f =ᶠ[𝓝 z] g) :
    (fun p ↦ hopfCollarRDeriv f p.1 p.2) =ᶠ[𝓝 z]
      (fun p ↦ hopfCollarRDeriv g p.1 p.2) := by
  filter_upwards [hfg.eventuallyEq_nhds] with p hp
  have hc : Tendsto (fun t : ℝ ↦ (t, p.2)) (𝓝 p.1) (𝓝 p) :=
    continuous_id.continuousAt.prodMk continuous_const.continuousAt
  exact (hp.comp_tendsto hc).deriv_eq

/-- Joint local equality preserves each actual old Hopf derivative as a JOINT germ.
The original period-one flow is continuous and equals the identity at time zero, so
pullback of each nearby joint germ gives native ordinary derivative congruence.
Source: original first/second/mixed collar jets in prop:collar, lines539–550. -/
theorem collarCK_hopfDeriv_germ (i : Fin a)
    {f g : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)}
    {z : ℝ × FreeHopfProduct C} (hfg : f =ᶠ[𝓝 z] g) :
    (fun p ↦ freeHopfDeriv C i (fun x ↦ f (p.1, x)) p.2) =ᶠ[𝓝 z]
      (fun p ↦ freeHopfDeriv C i (fun x ↦ g (p.1, x)) p.2) := by
  filter_upwards [hfg.eventuallyEq_nhds] with p hp
  have hc : Continuous (fun t : ℝ ↦ (p.1, freeHopfProductFlow C i t p.2)) :=
    continuous_const.prodMk ((freeHopfProductFlow_contMDiff C i).continuous.comp
      (continuous_id.prodMk continuous_const))
  have ht : Tendsto (fun t : ℝ ↦ (p.1, freeHopfProductFlow C i t p.2))
      (𝓝 0) (𝓝 p) := by
    have ht0 : Tendsto (fun t : ℝ ↦ (p.1, freeHopfProductFlow C i t p.2))
        (𝓝 0) (𝓝 (p.1, freeHopfProductFlow C i 0 p.2)) := hc.continuousAt
    simpa only [freeHopfProductFlow_zero, Prod.mk.eta] using ht0
  exact (hp.comp_tendsto ht).deriv_eq

/-- A joint germ identifies the FULL actual square columns, including the normal,
first and once-indexed sorted-second columns with every diagonal retained. Iterate
the actual Hopf derivative germ fact; no point-value differentiation is used.
Source: prop:collar, square pairing in lines539–546. -/
theorem collarCK_squareColumns_eq_of_germ
    {f g : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)}
    {z : ℝ × FreeHopfProduct C} (hfg : f =ᶠ[𝓝 z] g) :
    hopfCollarSquareColumns C f z.1 z.2 = hopfCollarSquareColumns C g z.1 z.2 := by
  funext k
  rcases k with k | (i | ij)
  · exact (collarCK_rDeriv_germ C hfg).self_of_nhds
  · exact (collarCK_hopfDeriv_germ C i hfg).self_of_nhds
  · exact (collarCK_hopfDeriv_germ C ij.val.1
      (collarCK_hopfDeriv_germ C ij.val.2 hfg)).self_of_nhds

/-- The literal original square pairing agrees for functions with the same joint
germ, since its actual full columns agree. Source: equation(5.3), lines539–549. -/
theorem collarCK_squarePairing_eq_of_germ
    {f g : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)}
    {z : ℝ × FreeHopfProduct C} (hfg : f =ᶠ[𝓝 z] g) :
    hopfCollarSquarePairing C f z.1 z.2 = hopfCollarSquarePairing C g z.1 z.2 := by
  unfold hopfCollarSquarePairing
  rw [collarCK_squareColumns_eq_of_germ C hfg]

/-- The original actual forcing agrees for equal joint germs. Its sorted-second
rows are real inner products of the same actual mixed Hopf/normal derivatives.
Source: equation(5.3), lines539–549. -/
theorem collarCK_squareForcing_eq_of_germ
    {f g : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)}
    {z : ℝ × FreeHopfProduct C} (hfg : f =ᶠ[𝓝 z] g) :
    hopfCollarSquareForcing C f z.1 z.2 = hopfCollarSquareForcing C g z.1 z.2 := by
  have hm (i : Fin a) : freeHopfDeriv C i (hopfCollarRDeriv f z.1) z.2 =
      freeHopfDeriv C i (hopfCollarRDeriv g z.1) z.2 :=
    (collarCK_hopfDeriv_germ C i (collarCK_rDeriv_germ C hfg)).self_of_nhds
  unfold hopfCollarSquareForcing
  congr 1
  funext k
  rcases k with k | (i | ij)
  · rfl
  · rfl
  · change inner ℝ _ _ = inner ℝ _ _
    rw [hm ij.val.1, hm ij.val.2]

/-- A joint germ transfers the actual inverse PDE and its actual noncharacteristic
square operator, with no desired metric identity as a premise. Repeated normal
derivative congruence gives acceleration; the literal pairing and forcing agree.
Source: equation(5.3) and retained invertibility, lines539–550. -/
theorem collarCK_inversePDE_of_germ
    {f g : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)}
    {z : ℝ × FreeHopfProduct C} (hfg : f =ᶠ[𝓝 z] g)
    (hinv : (hopfCollarSquarePairing C g z.1 z.2).IsInvertible)
    (hPDE : deriv (fun t ↦ hopfCollarRDeriv g t z.2) z.1 =
      (hopfCollarSquarePairing C g z.1 z.2).inverse
        (hopfCollarSquareForcing C g z.1 z.2)) :
    (hopfCollarSquarePairing C f z.1 z.2).IsInvertible ∧
      deriv (fun t ↦ hopfCollarRDeriv f t z.2) z.1 =
        (hopfCollarSquarePairing C f z.1 z.2).inverse
          (hopfCollarSquareForcing C f z.1 z.2) := by
  have hrr := (collarCK_rDeriv_germ C (collarCK_rDeriv_germ C hfg)).self_of_nhds
  rw [collarCK_squarePairing_eq_of_germ C hfg, collarCK_squareForcing_eq_of_germ C hfg]
  exact ⟨hinv, hrr.trans hPDE⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCK_local_time_analytic
#print axioms GlobalEmbedding.Paper.collarCK_local_tubes_overlap
#print axioms GlobalEmbedding.Paper.collarCK_compact_germ_gluing
#print axioms GlobalEmbedding.Paper.collarCK_rDeriv_germ
#print axioms GlobalEmbedding.Paper.collarCK_hopfDeriv_germ
#print axioms GlobalEmbedding.Paper.collarCK_squareColumns_eq_of_germ
#print axioms GlobalEmbedding.Paper.collarCK_squarePairing_eq_of_germ
#print axioms GlobalEmbedding.Paper.collarCK_squareForcing_eq_of_germ
#print axioms GlobalEmbedding.Paper.collarCK_inversePDE_of_germ
