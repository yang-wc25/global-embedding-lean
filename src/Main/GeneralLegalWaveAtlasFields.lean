import Main.GeneralLegalWaveAbsorption
import Upgrade.IncidenceAtlasLeading

/-!
# Native leading tensors for arbitrary smooth legal cutoffs

The input is the paper's supported smooth cutoff and its locally smooth
phase and actual normal section. No radial bump, preferred center,
global uncut phase smoothness or output bound is assumed.

The algebra uses the existing native symmetric-square tensor and actual
inverse atlas frame. Smoothness is proved only after expressing that tensor
in the fixed chart; this avoids any false global assertion about the
pointwise native tangent trivialization. Compactness then manufactures one
bound on every original atlas sample, chosen before any probe scale.

Provenance: the frozen `Upgrade.IncidenceLegalFields`,
`Upgrade.IncidenceAtlasLeading` and `NormalPolar.FullResponseBounds` proofs
for normalized chart bumps. Their underlying tensor algebra is reused;
only their supported-cutoff input is generalized here.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation
open Paper Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

namespace OpenSupportedLegalWave

@[simp] theorem ofLocal_tensor [T2Space M]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ,V) ∞ F}
    (w : LocalLegalWave (n := n) F hF) (x : M) :
    (ofLocal w).tensor x = w.tensor x := rfl

/-- Leading values stay in the original actual normal space at every point. -/
theorem value_mem_normal
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF) (z : M) :
    w.value z ∈ normalSpace (I := IM) F z :=
  (normalSpace (I := IM) F z).smul_mem (w.cutoff z) (w.normal z).property

theorem tensor_in_frame
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF)
    (z : M) (frame : E →L[ℝ] E) :
    probeTensorInFrame frame (w.tensor z) =
      w.cutoff z • incidenceLegalTensor
        ((mfderiv IM 𝓘(ℝ, ℝ) w.phase z).comp frame) (w.normal z : V) := by
  have hw : w.tensor z = w.cutoff z •
      incidenceLegalTensor (mfderiv IM 𝓘(ℝ, ℝ) w.phase z) (w.normal z : V) := by
    apply ContinuousLinearMap.ext
    intro q
    rfl
  rw [probeTensorInFrame, hw, ContinuousLinearMap.smul_comp]
  simpa only [] using! congrArg
    (fun L : SymmetricSquare E →L[ℝ] V ↦ w.cutoff z • L)
    (incidenceLegalTensor_comp_square
      (show E →L[ℝ] ℝ from mfderiv IM 𝓘(ℝ, ℝ) w.phase z) (w.normal z : V) frame)

/-- At an actual atlas point the covector in the inverse source frame is the
ordinary derivative of the SAME phase composed with that chart inverse. -/
theorem phase_covector_in_atlas
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : E) (hz : z ∈ (A.chart i).target) (hw : (A.chart i).symm z ∈ w.domain) :
    (mfderiv IM 𝓘(ℝ, ℝ) w.phase ((A.chart i).symm z)).comp
      (probeAtlasFrame A i ((A.chart i).symm z)) =
        fderiv ℝ (w.phase ∘ (A.chart i).symm) z := by
  have hp := ((w.phase_smooth _ hw).contMDiffAt
    (w.domain_open.mem_nhds hw)).mdifferentiableAt (by simp)
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i) hz).mdifferentiableAt
    (by simp)
  rw [probeAtlasFrame, (A.chart i).right_inv hz]
  simpa only [mfderiv_eq_fderiv] using! (mfderiv_comp z hp hc).symm

/-- The literal tensor leading field in one selected atlas coordinate chart. -/
def atlasLeadingTensor
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF)
    (A : BufferedAtlas M E) (i : Fin A.count) (z : E) : SymmetricSquare E →L[ℝ] V :=
  w.cutoff ((A.chart i).symm z) • incidenceLegalTensor
    (fderiv ℝ (w.phase ∘ (A.chart i).symm) z) (w.normal ((A.chart i).symm z) : V)

/-- The coordinate expression is the same actual tensor and actual inverse
frame, even where the un-cut phase was not required to be smooth. -/
theorem atlasLeadingTensor_eq
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : E) (hz : z ∈ (A.chart i).target) :
    w.atlasLeadingTensor A i z =
      probeTensorInFrame (probeAtlasFrame A i ((A.chart i).symm z))
        (w.tensor ((A.chart i).symm z)) := by
  rw [w.tensor_in_frame]
  by_cases hs : (A.chart i).symm z ∈ tsupport w.cutoff
  · have hd := w.phase_covector_in_atlas A hA i z hz (w.support_subset hs)
    unfold atlasLeadingTensor
    rw [hd]
  · simp only [atlasLeadingTensor, image_eq_zero_of_notMem_tsupport hs]
    apply ContinuousLinearMap.ext
    intro q
    change (0 : ℝ) • (_ : V) = (0 : ℝ) • (_ : V)
    rw [zero_smul, zero_smul]

/-- Actual tensor leading fields are smooth on the selected atlas target.
The proof uses no smoothness assertion about arbitrary native tangent charts. -/
theorem atlasLeadingTensor_contDiffOn [T2Space M]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (w.atlasLeadingTensor A i) (A.chart i).target := by
  intro z hz
  have hcinv : ContMDiffAt IM IM ∞ (A.chart i).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i) hz
  have hcut : ContDiffAt ℝ ∞ (fun s ↦ w.cutoff ((A.chart i).symm s)) z :=
    (w.cutoff_smooth.contMDiffAt.comp z hcinv).contDiffAt
  by_cases hs : (A.chart i).symm z ∈ tsupport w.cutoff
  · have hd := w.support_subset hs
    have hphase : ContDiffAt ℝ ∞ (w.phase ∘ (A.chart i).symm) z :=
      (((w.phase_smooth _ hd).contMDiffAt (w.domain_open.mem_nhds hd)).comp z hcinv).contDiffAt
    have hcov : ContDiffAt ℝ ∞ (fderiv ℝ (w.phase ∘ (A.chart i).symm)) z :=
      hphase.fderiv_right (by simp)
    have hnu : ContDiffAt ℝ ∞
        (fun s ↦ (w.normal ((A.chart i).symm s) : V)) z :=
      (((w.normal_smooth _ hd).contMDiffAt (w.domain_open.mem_nhds hd)).comp z hcinv).contDiffAt
    exact (hcut.smul (contDiff_incidenceLegalTensor.contDiffAt.comp z
      (hcov.prodMk hnu))).contDiffWithinAt
  · have hzero : ∀ᶠ s in 𝓝 z, w.cutoff ((A.chart i).symm s) = 0 := by
      have hne : ∀ᶠ p in 𝓝 ((A.chart i).symm z), p ∉ tsupport w.cutoff :=
        (isClosed_tsupport w.cutoff).isOpen_compl.mem_nhds hs
      filter_upwards [hcinv.continuousAt.eventually hne] with s hs'
      exact image_eq_zero_of_notMem_tsupport hs'
    apply ((contDiffAt_const (c := (0 : SymmetricSquare E →L[ℝ] V))).congr_of_eventuallyEq
      ?_).contDiffWithinAt
    filter_upwards [hzero] with s hs'
    simp only [atlasLeadingTensor, hs']
    apply ContinuousLinearMap.ext
    intro q
    change (0 : ℝ) • _ = (0 : V)
    exact zero_smul ℝ _

/-- The actual atlas-coordinate leading values are smooth on the same target. -/
theorem atlasLeadingValue_contDiffOn [T2Space M]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (w.value ∘ (A.chart i).symm) (A.chart i).target := by
  intro z hz
  exact (w.value_contMDiff.contMDiffAt.comp z
    (contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i) hz)).contDiffAt.contDiffWithinAt

/-- The fixed center normalization preserves smoothness of this actual
operator field; no derivative of the fixed right factor is inserted. -/
theorem normalizedAtlasLeadingTensor_contDiffOn [T2Space M]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : OpenSupportedLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) :
    ContDiffOn ℝ ∞
      (fun z ↦ probeTensorInFrame
        (probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm z))
          (w.tensor ((A.chart i).symm z))) (A.chart i).target := by
  have h := (w.atlasLeadingTensor_contDiffOn A hA i).clm_comp
    (contDiffOn_const (c := probeAtlasNormalizationSquare A hA i x hx))
  apply h.congr
  intro z hz
  rw [probeTensorInFrame_normalized, ← w.atlasLeadingTensor_eq A hA i z hz]


end OpenSupportedLegalWave

/-- One finite reference constant bounds every actual leading wave tensor
in every original inverse chart frame on its compact support. -/
theorem exists_uniform_general_wave_tensor_in_frame_bound [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {r : ℕ} (waves : Fin r → OpenSupportedLegalWave F₀ hF₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ l i x, x ∈ A.support i →
      ‖probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤ B := by
  have hc (l : Fin r) (i : Fin A.count) : ContinuousOn
      (fun x ↦ probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x))
      (A.support i) := by
    have hcoord := ((waves l).atlasLeadingTensor_contDiffOn A hA i).continuousOn.comp
      (A.chart i).continuousOn (fun x hx ↦ (A.chart i).map_source hx)
    have hsource : ContinuousOn
        (fun x ↦ probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x))
        (A.chart i).source := by
      apply hcoord.congr
      intro x hx
      symm
      simpa only [Function.comp_apply, (A.chart i).left_inv hx] using
        (waves l).atlasLeadingTensor_eq A hA i (A.chart i x) ((A.chart i).map_source hx)
    exact hsource.mono (hA.support_subset i)
  choose B hB using fun k : Fin r × Fin A.count ↦
    (hcompact k.2).exists_bound_of_continuousOn (hc k.1 k.2)
  obtain ⟨K, hK⟩ := Finite.exists_le B
  refine ⟨|K| + 1, by positivity, ?_⟩
  intro l i x hx
  exact (hB (l, i) x hx).trans ((hK (l, i)).trans ((le_abs_self K).trans (by linarith)))


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.tensor_in_frame
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.phase_covector_in_atlas
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.atlasLeadingTensor_eq
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.atlasLeadingTensor_contDiffOn
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.normalizedAtlasLeadingTensor_contDiffOn
#print axioms GlobalEmbedding.Continuation.exists_uniform_general_wave_tensor_in_frame_bound
