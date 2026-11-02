import Upgrade.CompactFixedAtlasPhaseGeometry
import GlobalEmbedding.Paper.FrameGramInverseIdentities
import GlobalEmbedding.Offline.CoincidenceAvoidanceEmbedding

/-!
# The actual tangent left inverse under exact metric perturbations

The Gram matrix in the fixed source atlas is literally preserved by the original
induced-metric equality. Its inverse is therefore the reference inverse, even
when the actual tangent image rotates. Compact reference supports give a uniform
bound for every same-metric perturbation. No normal identification or derivative
of that identification is assumed here.
-/

noncomputable section
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Exact metric preservation retains the full Gram operator in the same actual
source frame, not just a lower spectral bound. -/
theorem probeAtlasFirstJet_gram_eq_of_inducedMetric_eq
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (hmetric : inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) :
    (probeAtlasFirstJet A G i x).adjoint.comp (probeAtlasFirstJet A G i x) =
      (probeAtlasFirstJet A F i x).adjoint.comp (probeAtlasFirstJet A F i x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [probeAtlasFirstJet_eq_mfderiv_frame A hA G hG i x hx,
    probeAtlasFirstJet_eq_mfderiv_frame A hA F hF i x hx]
  have heq := congrArg (fun b ↦ b (probeAtlasFrame A i x w) (probeAtlasFrame A i x v)) hmetric
  exact heq

/-- The actual Gram coefficient operator. It is the canonical left inverse of
the actual fixed-chart first jet whenever that jet is injective. -/
def probeAtlasTangentLeftInverse (A : BufferedAtlas M E) (F : M → V)
    (i : Fin A.count) (x : M) : V →L[ℝ] E :=
  ((probeAtlasFirstJet A F i x).adjoint.comp
    (probeAtlasFirstJet A F i x)).inverse.comp (probeAtlasFirstJet A F i x).adjoint

theorem probeAtlasTangentLeftInverse_identities
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) :
    (probeAtlasTangentLeftInverse A F i x).comp (probeAtlasFirstJet A F i x) =
      ContinuousLinearMap.id ℝ E ∧
    (probeAtlasFirstJet A F i x).comp (probeAtlasTangentLeftInverse A F i x) =
      (probeAtlasFirstJet A F i x).range.starProjection :=
  frame_gram_inverse_identities _ (probeAtlasFirstJet_injective A hA F hF i x hx himm)

theorem probeAtlasFirstJet_norm_eq_of_inducedMetric_eq
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (hmetric : inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) :
    ‖probeAtlasFirstJet A G i x‖ = ‖probeAtlasFirstJet A F i x‖ := by
  have hgram := probeAtlasFirstJet_gram_eq_of_inducedMetric_eq A hA F G hF hG i x hx hmetric
  have heq := congrArg norm hgram
  rw [ContinuousLinearMap.norm_adjoint_comp_self,
    ContinuousLinearMap.norm_adjoint_comp_self] at heq
  nlinarith [norm_nonneg (probeAtlasFirstJet A G i x),
    norm_nonneg (probeAtlasFirstJet A F i x)]

theorem probeAtlasTangentLeftInverse_norm_le_reference
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F G : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (hmetric : inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) :
    ‖probeAtlasTangentLeftInverse A G i x‖ ≤
      ‖((probeAtlasFirstJet A F i x).adjoint.comp
        (probeAtlasFirstJet A F i x)).inverse‖ * ‖probeAtlasFirstJet A F i x‖ := by
  unfold probeAtlasTangentLeftInverse
  rw [probeAtlasFirstJet_gram_eq_of_inducedMetric_eq A hA F G hF hG i x hx hmetric]
  calc
    _ ≤ ‖((probeAtlasFirstJet A F i x).adjoint.comp
        (probeAtlasFirstJet A F i x)).inverse‖ * ‖(probeAtlasFirstJet A G i x).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map,
      probeAtlasFirstJet_norm_eq_of_inducedMetric_eq A hA F G hF hG i x hx hmetric]

end GlobalEmbedding.Upgrade
