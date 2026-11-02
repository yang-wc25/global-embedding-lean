import Probes.Round3ParameterChartPullback

/-! Transport the actual subordinate cutoff through an actual parameter
chart. A genuine closed carrier supplies the zero germs outside the source.
This is used on primitive eta before the free datum is formed; no computed
wave or increment is multiplied by an extra cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def round3ParameterSupportedPullback (q : OpenPartialHomeomorph X Y) (f : Y → ℝ) (x : X) : ℝ :=
  if x ∈ q.source then f (q x) else 0

theorem round3ParameterSupportedPullback_support
    (q : OpenPartialHomeomorph X Y) (f : Y → ℝ) (C : Set X)
    (hC : IsClosed C)
    (hSupport : ∀ x ∈ q.source, q x ∈ tsupport f → x ∈ C) :
    tsupport (round3ParameterSupportedPullback q f) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  change round3ParameterSupportedPullback q f x ≠ 0 at hx
  by_cases hqx : x ∈ q.source
  · apply hSupport x hqx
    apply subset_tsupport
    change f (q x) ≠ 0
    simpa only [round3ParameterSupportedPullback,ite_eq_left hqx] using hx
  · exact (hx (by simp only [round3ParameterSupportedPullback,ite_eq_right hqx])).elim

theorem round3ParameterSupportedPullback_tsupport_iff
    (q : OpenPartialHomeomorph X Y) (f : Y → ℝ) (x : X) (hx : x ∈ q.source) :
    x ∈ tsupport (round3ParameterSupportedPullback q f) ↔ q x ∈ tsupport f := by
  constructor
  · intro hs
    by_contra hn
    have hzero := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
      (q.continuousOn.continuousAt (q.open_source.mem_nhds hx))
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hs
    filter_upwards [hzero,q.open_source.mem_nhds hx] with y hy hys
    simpa only [Function.comp_apply,Pi.zero_apply,round3ParameterSupportedPullback,ite_eq_left hys] using hy
  · intro hs
    by_contra hn
    have hc : Tendsto q.symm (𝓝 (q x)) (𝓝 x) := by
      simpa only [ContinuousAt,q.left_inv hx] using
        (q.symm.continuousOn.continuousAt (q.open_target.mem_nhds (q.map_source hx)))
    have hzero := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hc
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hs
    filter_upwards [hzero,q.open_target.mem_nhds (q.map_source hx)] with y hy hyt
    simpa only [Function.comp_apply,Pi.zero_apply,round3ParameterSupportedPullback,
      ite_eq_left (q.map_target hyt),q.right_inv hyt] using hy

variable {E F HX HY : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HX] [TopologicalSpace HY]
  {I : ModelWithCorners ℝ E HX} {J : ModelWithCorners ℝ F HY}
  [ChartedSpace HX X] [ChartedSpace HY Y]

theorem round3ParameterSupportedPullback_smooth
    (q : OpenPartialHomeomorph X Y) (f : Y → ℝ) (C : Set X)
    (hC : IsClosed C) (hCS : C ⊆ q.source)
    (hSupport : ∀ x ∈ q.source, q x ∈ tsupport f → x ∈ C)
    (hq : ContMDiffOn I J ∞ q q.source)
    (hf : ContMDiffOn J 𝓘(ℝ,ℝ) ∞ f q.target) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (round3ParameterSupportedPullback q f) := by
  have hsup := round3ParameterSupportedPullback_support q f C hC hSupport
  intro x
  by_cases hqx : x ∈ q.source
  · have hc := (hf.comp hq q.mapsTo).contMDiffAt (q.open_source.mem_nhds hqx)
    apply hc.congr_of_eventuallyEq
    filter_upwards [q.open_source.mem_nhds hqx] with y hy
    exact ite_eq_left hy
  · have hxC : x ∉ C := fun hx => hqx (hCS hx)
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hC.isOpen_compl.mem_nhds hxC] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun hs => hy (hsup hs))

theorem round3ParameterSupportedPullback_compact_smooth
    [T2Space X] (q : OpenPartialHomeomorph X Y) (f : Y → ℝ)
    (hfCompact : IsCompact (tsupport f)) (hfSupport : tsupport f ⊆ q.target)
    (hq : ContMDiffOn I J ∞ q q.source)
    (hf : ContMDiffOn J 𝓘(ℝ,ℝ) ∞ f q.target) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (round3ParameterSupportedPullback q f) ∧
    IsCompact (tsupport (round3ParameterSupportedPullback q f)) ∧
    tsupport (round3ParameterSupportedPullback q f) ⊆ q.symm '' tsupport f := by
  let C := q.symm '' tsupport f
  have hC : IsCompact C := hfCompact.image_of_continuousOn (q.symm.continuousOn.mono hfSupport)
  have hCS : C ⊆ q.source := by
    rintro _ ⟨y,hy,rfl⟩
    exact q.map_target (hfSupport hy)
  have hs : ∀ x ∈ q.source, q x ∈ tsupport f → x ∈ C := by
    intro x hx hfx
    exact ⟨q x,hfx,q.left_inv hx⟩
  have hsup := round3ParameterSupportedPullback_support q f C hC.isClosed hs
  exact ⟨round3ParameterSupportedPullback_smooth q f C hC.isClosed hCS hs hq hf,
    hC.of_isClosed_subset (isClosed_tsupport _) hsup,hsup⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterSupportedPullback_compact_smooth
