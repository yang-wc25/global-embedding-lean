import Main.GeneralLegalWaveAtlasFields
import Round2.ProbeBridgeSecondForm

/-!
# Arbitrary-cutoff native Hessian response to the actual identified second form

The original rank-one Hessian lift and old-normal projection identities
hold for the paper's arbitrary supported smooth cutoff. The existing
operator product-rule estimate then converts its native Hessian response
using the same actual geometric family and normal identification.
No response, normality or moving-normal derivative is postulated.
-/
noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
open Paper Upgrade GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance generalBridgeBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance generalBridgeBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance generalBridgeBilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

namespace OpenSupportedLegalWave

/-- The actual first-block Hessian principal tensor in any atlas source is
exactly the original legal tensor in that atlas's inverse tangent frame.
No differentiability of the phase outside the legal domain is assumed: its
cutoff-normal amplitude, and hence both tensors, vanish there. The existing
`atlasLeadingTensor_eq` theorem supplies this support-sensitive identity. -/
theorem actualHessianLift_phaseRankOneHessian_in_atlas
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (wave : OpenSupportedLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : M) (hz : z ∈ (A.chart i).source) :
    actualHessianLift
      (phaseRankOneHessian (wave.phase ∘ (A.chart i).symm)
        (wave.value ∘ (A.chart i).symm) (A.chart i z)) =
      probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z) := by
  rw [actualHessianLift_phaseRankOneHessian]
  calc
    _ = wave.atlasLeadingTensor A i (A.chart i z) :=
      incidenceLegalTensor_smul_normal _ _ _
    _ = probeTensorInFrame (probeAtlasFrame A i ((A.chart i).symm (A.chart i z)))
        (wave.tensor ((A.chart i).symm (A.chart i z))) :=
      wave.atlasLeadingTensor_eq A hA i (A.chart i z) ((A.chart i).map_source hz)
    _ = _ := congrArg
      (fun y : M ↦ probeTensorInFrame (probeAtlasFrame A i y) (wave.tensor y))
      ((A.chart i).left_inv hz)

/-- The actual transported legal principal tensor remains in the old
normal space. This is proved from its literal normal section, not a rank
or a supplied principal-normality hypothesis. -/
theorem normalProjection_comp_tensor_in_frame
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (wave : OpenSupportedLegalWave F hF) (z : M) (frame : E →L[ℝ] E) :
    (normalSpace (I := IM) F z).starProjection.comp
      (probeTensorInFrame frame (wave.tensor z)) =
        probeTensorInFrame frame (wave.tensor z) := by
  apply ContinuousLinearMap.ext
  intro q
  apply (normalSpace (I := IM) F z).starProjection_eq_self_iff.mpr
  change wave.cutoff z •
    (supportedRankCovectorSquare (mfderiv IM 𝓘(ℝ, ℝ) wave.phase z).toLinearMap
      (symmetricSquareLinearMap frame.toLinearMap q) • (wave.normal z : V)) ∈
    normalSpace (I := IM) F z
  exact (normalSpace (I := IM) F z).smul_mem _
    ((normalSpace (I := IM) F z).smul_mem _ (wave.normal z).property)


end OpenSupportedLegalWave

/-- The complete geometric conversion of an actual native bilinear
Hessian response into the exact operator-norm expression required by probes.
Every error on the right is a native error of the same map or identification.
The legal principal tensor and its old-normal projection identity are proved
from the actual wave. -/
theorem generalProbeGeometry_identified_secondForm_response_native_bound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r) (wave : OpenSupportedLegalWave F₀ hF₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) (coefficient : ℝ) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d -
        coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ ≤
      actualHessianLiftConstant E V *
        ‖fderiv ℝ
          (fun v ↦ fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)) u d -
          coefficient • phaseRankOneHessian (wave.phase ∘ (A.chart i).symm)
            (wave.value ∘ (A.chart i).symm) (A.chart i z)‖ +
      ‖normalIdentificationOperator (n := n) F₀ (g.map t u) (g.normalIdentification t u) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ *
        ‖coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ +
      ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (g.map t v)
          (g.normalIdentification t v) z) u d‖ *
        ‖probeAtlasSecondJet A (g.map t u) i z‖ := by
  obtain ⟨hQ, hH⟩ := g.atlas_hessian_parameter_factors_differentiable A hA i t ht htt u hu z hz
  let Q := fun v : ProbeParameters r ↦ normalIdentificationOperator (n := n) F₀
    (g.map t v) (g.normalIdentification t v) z
  let H := fun v : ProbeParameters r ↦
    fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)
  let L := coefficient • phaseRankOneHessian (wave.phase ∘ (A.chart i).symm)
    (wave.value ∘ (A.chart i).symm) (A.chart i z)
  let T := coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)
  have hLT : actualHessianLift L = T := by
    dsimp only [L, T]
    rw [map_smul, wave.actualHessianLift_phaseRankOneHessian_in_atlas A hA i z hz]
  have hT : (normalSpace (I := IM) F₀ z).starProjection.comp T = T := by
    dsimp only [T]
    rw [ContinuousLinearMap.comp_smul, wave.normalProjection_comp_tensor_in_frame]
  have hLH : HasFDerivAt (fun v ↦ actualHessianLift (H v))
      ((actualHessianLift («E» := E) (F := V)).comp (fderiv ℝ H u)) u :=
    (actualHessianLift («E» := E) (F := V)).hasFDerivAt.comp u hH.hasFDerivAt
  have hnorm := norm_parameter_identified_operator_response_sub_le Q
    (fun v ↦ actualHessianLift (H v)) (normalSpace (I := IM) F₀ z).starProjection
    T u d hQ hLH.differentiableAt
    (normalIdentificationOperator_norm_le_one F₀ (g.map t u) (g.normalIdentification t u) z) hT
  have hderiv : fderiv ℝ (fun v ↦ actualHessianLift (H v)) u d =
      actualHessianLift (fderiv ℝ H u d) := by
    exact congrArg
      (fun D : ProbeParameters r →L[ℝ] (SymmetricSquare E →L[ℝ] V) ↦ D d) hLH.fderiv
  have hraw : ‖fderiv ℝ (fun v ↦ actualHessianLift (H v)) u d - T‖ ≤
      actualHessianLiftConstant E V * ‖fderiv ℝ H u d - L‖ := by
    rw [hderiv, ← hLT]
    exact actualHessianLift_sub_norm_le _ _
  have heq : (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
      (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) z)) =
      fun v ↦ (Q v).comp (actualHessianLift (H v)) := by
    funext v
    exact identifiedTrueSecondForm_in_atlas_eq_identified_hessian F₀ (g.map t v)
      (g.slice_smooth t v) (g.normalIdentification t v) A hA i z hz
  rw [heq]
  exact hnorm.trans (add_le_add (add_le_add hraw le_rfl) le_rfl)


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.actualHessianLift_phaseRankOneHessian_in_atlas
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.normalProjection_comp_tensor_in_frame
#print axioms GlobalEmbedding.Continuation.generalProbeGeometry_identified_secondForm_response_native_bound
