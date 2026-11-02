import GlobalEmbedding.Paper.IncrementsModeFullReconstruction
import GlobalEmbedding.Paper.IncrementsActualReconstructionSupport
import GlobalEmbedding.Paper.IncrementsModeJointLocalReconstruction

/-!
# Stage 2: ORIGINAL relative supported reconstruction in its actual joint chart

Source: main.tex594–609,617–650, lem:increments. Exclusive worker W5.
Statement ONLY for ROOT lock, with one expected named proof hole.
No generic extension carrier, output cutoff or output regularity premise.
-/

noncomputable section
open Manifold
open scoped ContDiff Classical

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

omit [IsManifold I ∞ M] [BoundarylessManifold I M] in
/-- Ordinary public exposure of the EXISTING relative supported-chart transport
body used below for the two actual full reconstruction channels. The original
conditional extension is jointly smooth ON W, with native W-relative support
inside K. Only the previously captured chart/open/relative-closed/zero data are
arguments; no source-in-W or inverse/geometry-field hypothesis is added.

Source: main.tex594–609,617–650, lem:increments, support and finite parameters;
accepted original IncrementsModeSupportedChartPullback local hfinish189–220.
Natural-language proof: this is that same existing body MOVED ONCE. The literal
extension is zero outside K. Native closure_minimal in the W subtype gives its
relative support. Within the chart source, compose actual target-smooth Z with
the actual smooth chart. Outside the chart source, K being inside that source
and relatively closed in W supplies a genuine open zero neighborhood inside W.
Native eventual equality with zero gives joint smoothness there. No claim is
made outside W or at its parameter boundary. Empty chart/K and zero-dimensional
fibers are unchanged. Actual correction consumers must derive their Z regularity
and zero condition from original source data; this exposure does not construct
those consumers, a new extension framework, stronger support or new cutoff. -/
theorem increments_supported_smooth_chart_pullback
    (a : OpenPartialHomeomorph (Ep × M) (Ep × D))
    (W K : Set (Ep × M)) (_hW : IsOpen W)
    (_hK : IsClosed (Subtype.val ⁻¹' K : Set W)) (_hKsource : K ⊆ a.source)
    (_hchart : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × D) ∞ a a.source)
    (Z : Ep × D → V) (hZ : ContDiffOn ℝ ∞ Z a.target)
    (hz : ∀ y ∈ a.source, y ∉ K → Z (a y) = 0) :
    let ext : Ep × M → V := fun y ↦ if y ∈ a.source then Z (a y) else 0
    ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ ext W ∧
      tsupport (fun y : W ↦ ext y) ⊆ Subtype.val ⁻¹' K := by
  let ext : Ep × M → V := fun y ↦ if y ∈ a.source then Z (a y) else 0
  have hezero (y : Ep × M) (_hy : y ∈ W) (hn : y ∉ K) : ext y = 0 := by
    by_cases hy : y ∈ a.source
    · exact (ite_eq_left hy).trans (hz y hy hn)
    · exact ite_eq_right hy
  have hsup : tsupport (fun y : W ↦ ext y) ⊆ Subtype.val ⁻¹' K := by
    apply closure_minimal _ _hK
    intro y hy
    by_contra hn
    exact hy (hezero y y.property hn)
  have hopen : IsOpen (Subtype.val '' (Subtype.val ⁻¹' K : Set W)ᶜ) :=
    _hW.isOpenMap_subtype_val _ _hK.isOpen_compl
  have hat (y : Ep × M) (hyW : y ∈ W) :
      ContMDiffAt ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ ext y := by
    by_cases hy : y ∈ a.source
    · have hc := hZ.contMDiffOn.comp _hchart (fun x hx ↦ a.map_source hx)
      apply (hc.contMDiffAt (a.open_source.mem_nhds hy)).congr_of_eventuallyEq
      filter_upwards [a.open_source.mem_nhds hy] with x hx
      exact ite_eq_left hx
    · have hn : y ∉ K := fun hk ↦ hy (_hKsource hk)
      have hym : y ∈ Subtype.val '' (Subtype.val ⁻¹' K : Set W)ᶜ :=
        ⟨⟨y, hyW⟩, hn, rfl⟩
      apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hym] with x hx
      rcases hx with ⟨w, hw, rfl⟩
      exact hezero w w.property hw
  exact ⟨fun y hy ↦ (hat y hy).contMDiffWithinAt, hsup⟩

/-- Pull back the SAME original finite reconstruction through its actual joint
chart and set it zero outside the chart source. On the ORIGINAL open W only,
relative closed joint support control of INPUT source/h/free-normal fields
implies joint smoothness, relative support control and exact chart values.

Source: main.tex594–609,617–650, local finite reconstruction and its original
support/localization and finite auxiliary parameter clauses.

Natural-language proof, pending ROOT lock of THIS statement: reuse the sole
actual joint finiteU/fullZ regularity theorem on a.target after normal publication.
For a point outside K, genuine INPUT localization and the actual chart inverse
identity exclude all original joint input supports. Native locality of the actual
finite differential expression, fixed real/imaginary channels and the accepted
fullZ support theorem make the literal output zero there; openness of the slice
and native derivative locality are used, not a hypothesis on desired output
support. Relative closedness of K IN W makes its W-complement an open zero
neighborhood
for points of W, including chart-boundary points inside W, since K is contained
in a.source. No claim is made at the parameter-open boundary outside W. Inside
the chart
source compose the actual jointly smooth local formula with the given actual
smooth chart. Native locality gives joint ContMDiffOn W only. Closure of the
nonzero set in the native subtype W lies in the preimage of K, giving support.
The two value identities
follow from the literal conditional and actual partial-chart inverse laws; the
chart source/target are open, so these identities also preserve the SAME germs.

The smooth chart and its inverse compatibility, actual joint G/J/T0/A/B/source
regularity and original RELATIVE closed input-support subordination are INTERNAL
original-data obligations. This does not construct an adapted chart or discharge
the full original profile/uniform estimates. No compactness of M or parameter
space, desired finiteU/Z/extension regularity or output support premise is added.
No global smoothness/support or input vanishing at the boundary of W is required.
No extra cutoff is multiplied onto any output. Empty chart/K, zero lengths/scales,
m=0 and N=0 are allowed. -/
theorem incrementsModeFullReconstruction_supported_chart_pullback
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : Ep × D → Source)
    (vfR vfI : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (c p x))
    (length : ℕ) (tau : ℝ)
    (a : OpenPartialHomeomorph (Ep × M) (Ep × D))
    (W : Set (Ep × M)) (_hW : IsOpen W) (_hsourceW : a.source ⊆ W)
    (K : Set (Ep × M))
    (_hK : IsClosed (Subtype.val ⁻¹' K : Set W)) (_hKsource : K ⊆ a.source)
    (_hchart : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × D) ∞ a a.source)
    (_hinverse : ∀ z ∈ a.target, a.symm z = (z.1, c z.1 z.2))
    (_hG : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) a.target)
    (_hJ : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) a.target)
    (_hT0 : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) a.target)
    (_hA : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (_hB : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (_hhR : ContDiffOn ℝ ∞ hR a.target) (_hhI : ContDiffOn ℝ ∞ hI a.target)
    (_hvfR : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vfR z.1 z.2 : V)) a.target)
    (_hvfI : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vfI z.1 z.2 : V)) a.target) :
    let source : Ep × D → Cdata := fun z ↦
      incrementsModeComplexInclude
          (incrementsModeSource (F z.1) (hF z.1) (c z.1)
            (fun x ↦ hR (z.1, x)) (vfR z.1) z.2) +
        Complex.I • incrementsModeComplexInclude
          (incrementsModeSource (F z.1) (hF z.1) (c z.1)
            (fun x ↦ hI (z.1, x)) (vfI z.1) z.2)
    ContDiffOn ℝ ∞ source a.target →
    (∀ z ∈ a.target,
      z ∈ tsupport source ∪ (tsupport hR ∪ (tsupport hI ∪
        (tsupport (fun w : Ep × D ↦ (vfR w.1 w.2 : V)) ∪
          tsupport (fun w : Ep × D ↦ (vfI w.1 w.2 : V))))) →
        a.symm z ∈ K) →
      let finiteU : Ep → D → Cdata := fun p ↦
        incrementsActualModeSum
          (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
          (incrementsModeComplexFirstOrderB (F p) (hF p) (c p))
          ((tau : ℂ) / Complex.I) length (fun x ↦ source (p, x))
      let ZR : Ep × D → V := fun z ↦
        incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
          (fun x ↦ incrementsModeRealPart (finiteU z.1 x))
          (fun x ↦ hR (z.1, x)) (vfR z.1) z.2
      let ZI : Ep × D → V := fun z ↦
        incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
          (fun x ↦ incrementsModeImagPart (finiteU z.1 x))
          (fun x ↦ hI (z.1, x)) (vfI z.1) z.2
      let extR : Ep × M → V := fun y ↦ if y ∈ a.source then ZR (a y) else 0
      let extI : Ep × M → V := fun y ↦ if y ∈ a.source then ZI (a y) else 0
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ extR W ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ extI W ∧
      tsupport (fun y : W ↦ extR y) ⊆ Subtype.val ⁻¹' K ∧
      tsupport (fun y : W ↦ extI y) ⊆ Subtype.val ⁻¹' K ∧
      (∀ y ∈ a.source, extR y = ZR (a y) ∧ extI y = ZI (a y)) ∧
      (∀ z ∈ a.target, extR (a.symm z) = ZR z ∧ extI (a.symm z) = ZI z) := by
  let source : Ep × D → Cdata := fun z ↦
    incrementsModeComplexInclude
        (incrementsModeSource (F z.1) (hF z.1) (c z.1)
          (fun x ↦ hR (z.1, x)) (vfR z.1) z.2) +
      Complex.I • incrementsModeComplexInclude
        (incrementsModeSource (F z.1) (hF z.1) (c z.1)
          (fun x ↦ hI (z.1, x)) (vfI z.1) z.2)
  change ContDiffOn ℝ ∞ source a.target → _
  intro hs hinput
  let finiteU : Ep → D → Cdata := fun p ↦
    incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
      (incrementsModeComplexFirstOrderB (F p) (hF p) (c p))
      ((tau : ℂ) / Complex.I) length (fun x ↦ source (p, x))
  let ZR : Ep × D → V := fun z ↦
    incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (fun x ↦ incrementsModeRealPart (finiteU z.1 x))
      (fun x ↦ hR (z.1, x)) (vfR z.1) z.2
  let ZI : Ep × D → V := fun z ↦
    incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (fun x ↦ incrementsModeImagPart (finiteU z.1 x))
      (fun x ↦ hI (z.1, x)) (vfI z.1) z.2
  have hlocal : ContDiffOn ℝ ∞ ZR a.target ∧ ContDiffOn ℝ ∞ ZI a.target :=
    incrementsModeFullReconstruction_joint_contDiffOn F hF c hR hI vfR vfI
      length tau a.target a.open_target _hG _hJ _hT0 _hA _hB _hhR _hhI _hvfR _hvfI hs
  have hslice {Y : Type} [Zero Y] (f : Ep × D → Y) (z : Ep × D)
      (hn : z ∉ tsupport f) : z.2 ∉ tsupport (fun x ↦ f (z.1, x)) := by
    intro hx
    exact hn (tsupport_comp_subset_preimage f
      (f := fun x : D ↦ (z.1, x)) (by fun_prop) hx)
  have hzero (y : Ep × M) (hy : y ∈ a.source) (hn : y ∉ K) :
      ZR (a y) = 0 ∧ ZI (a y) = 0 := by
    let z := a y
    have hz : z ∈ a.target := a.map_source hy
    have hin : z ∉ tsupport source ∪ (tsupport hR ∪ (tsupport hI ∪
        (tsupport (fun w : Ep × D ↦ (vfR w.1 w.2 : V)) ∪
          tsupport (fun w : Ep × D ↦ (vfI w.1 w.2 : V))))) := by
      intro h
      have hk := hinput z hz h
      exact hn (by simpa only [z, a.left_inv hy] using hk)
    have hout : z ∉ tsupport source ∧ z ∉ tsupport hR ∧ z ∉ tsupport hI ∧
        z ∉ tsupport (fun w : Ep × D ↦ (vfR w.1 w.2 : V)) ∧
        z ∉ tsupport (fun w : Ep × D ↦ (vfI w.1 w.2 : V)) := by
      simpa only [Set.mem_union, not_or] using hin
    have hu : z.2 ∉ tsupport (finiteU z.1) := by
      intro h
      exact hslice source z hout.1
        (increments_actual_mode_sum_tsupport _ _ _ length _ h)
    have hzchannel (ch : Cdata →L[ℝ] D) (h : Ep × D → Source)
        (vf : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (c p x))
        (hh : z ∉ tsupport h)
        (hv : z ∉ tsupport (fun w : Ep × D ↦ (vf w.1 w.2 : V))) :
        incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
          (fun x ↦ ch (finiteU z.1 x)) (fun x ↦ h (z.1, x)) (vf z.1) z.2 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hzout := incrementsModeFullReconstruction_tsupport
        (F z.1) (hF z.1) (c z.1) (fun x ↦ ch (finiteU z.1 x))
        (fun x ↦ h (z.1, x)) (vf z.1) ht
      rcases hzout with hc | hh' | hv'
      · exact hu (tsupport_comp_subset (g := ch) (map_zero ch) (finiteU z.1) hc)
      · exact hslice h z hh hh'
      · exact hslice (fun w : Ep × D ↦ (vf w.1 w.2 : V)) z hv hv'
    exact ⟨hzchannel incrementsModeRealPart hR vfR hout.2.1 hout.2.2.2.1,
      hzchannel incrementsModeImagPart hI vfI hout.2.2.1 hout.2.2.2.2⟩
  have hRout := increments_supported_smooth_chart_pullback
    a W K _hW _hK _hKsource _hchart ZR hlocal.1 (fun y hy hn ↦ (hzero y hy hn).1)
  have hIout := increments_supported_smooth_chart_pullback
    a W K _hW _hK _hKsource _hchart ZI hlocal.2 (fun y hy hn ↦ (hzero y hy hn).2)
  refine ⟨hRout.1, hIout.1, hRout.2, hIout.2, ?_, ?_⟩
  · intro y hy
    exact ⟨ite_eq_left hy, ite_eq_left hy⟩
  · intro z hz
    change (if a.symm z ∈ a.source then ZR (a (a.symm z)) else 0) = ZR z ∧
      (if a.symm z ∈ a.source then ZI (a (a.symm z)) else 0) = ZI z
    exact ⟨(ite_eq_left (a.map_target hz)).trans (congrArg ZR (a.right_inv hz)),
      (ite_eq_left (a.map_target hz)).trans (congrArg ZI (a.right_inv hz))⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_supported_chart_pullback

#print axioms GlobalEmbedding.Paper.increments_supported_smooth_chart_pullback
