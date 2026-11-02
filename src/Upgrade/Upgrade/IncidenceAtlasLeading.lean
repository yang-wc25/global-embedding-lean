import Upgrade.IncidenceLegalFields

/-!
# Actual legal principal fields in the chosen fixed atlas

The chart derivative of the original phase, the cutoff, and the same normal
section give a smooth leading tensor. It equals the native tensor in the
actual inverse source frame. This supplies the missing leading-field
variation term when one fixed packet is used on a neighborhood of its center.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

namespace LocalLegalWave

/-- The literal tensor leading field in one selected atlas coordinate chart. -/
def atlasLeadingTensor
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (i : Fin A.count) (z : E) : SymmetricSquare E →L[ℝ] V :=
  w.cutoff ((A.chart i).symm z) • incidenceLegalTensor
    (fderiv ℝ (w.phase ∘ (A.chart i).symm) z) (w.normal ((A.chart i).symm z) : V)

/-- The coordinate expression is the same actual tensor and actual inverse
frame, even where the un-cut phase was not required to be smooth. -/
theorem atlasLeadingTensor_eq
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : E) (hz : z ∈ (A.chart i).target) :
    w.atlasLeadingTensor A i z =
      probeTensorInFrame (probeAtlasFrame A i ((A.chart i).symm z))
        (w.tensor ((A.chart i).symm z)) := by
  rw [w.tensor_in_frame]
  by_cases hs : (A.chart i).symm z ∈ tsupport (w.cutoff : M → ℝ)
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
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (w.atlasLeadingTensor A i) (A.chart i).target := by
  intro z hz
  have hcinv : ContMDiffAt IM IM ∞ (A.chart i).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i) hz
  have hcut : ContDiffAt ℝ ∞ (fun s ↦ w.cutoff ((A.chart i).symm s)) z :=
    (w.cutoff.contMDiffAt.comp z hcinv).contDiffAt
  by_cases hs : (A.chart i).symm z ∈ tsupport (w.cutoff : M → ℝ)
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
      have hne : ∀ᶠ p in 𝓝 ((A.chart i).symm z), p ∉ tsupport (w.cutoff : M → ℝ) :=
        (isClosed_tsupport (w.cutoff : M → ℝ)).isOpen_compl.mem_nhds hs
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
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (w.value ∘ (A.chart i).symm) (A.chart i).target := by
  intro z hz
  exact (w.value_contMDiff.contMDiffAt.comp z
    (contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i) hz)).contDiffAt.contDiffWithinAt

/-- The fixed center normalization preserves smoothness of this actual
operator field; no derivative of the fixed right factor is inserted. -/
theorem normalizedAtlasLeadingTensor_contDiffOn [T2Space M]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
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

end LocalLegalWave
end GlobalEmbedding.Upgrade
