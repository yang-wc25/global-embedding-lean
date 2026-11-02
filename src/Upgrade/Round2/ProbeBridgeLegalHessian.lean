import Upgrade.IncidenceAtlasLeading
import GlobalEmbedding.Offline.ActualHessianJet
import Probes.ActualOscillatoryRemainder

/-!
# The actual probe Hessian principal term in the original atlas frame

The upstream first-block estimates use `phaseRankOneHessian`, with the native
continuous bilinear operator norm. The upgrade response uses the unchanged
`SymmetricSquare` quotient operator norm and the actual inverse atlas frame.
This file proves their exact geometric identification, including points
outside a wave's legal chart where its cutoff is zero. No probe family,
normal identification, or analytic remainder is constructed here.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology TensorProduct

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The upstream bilinear principal tensor descends to the original legal
rank-one operator with its exact normalization. -/
theorem actualHessianLift_phaseRankOneHessian
    (phase : E → ℝ) (amplitude : E → V) (x : E) :
    actualHessianLift (phaseRankOneHessian phase amplitude x) =
      incidenceLegalTensor (fderiv ℝ phase x) (amplitude x) := by
  have hsym : ∀ v w, phaseRankOneHessian phase amplitude x v w =
      phaseRankOneHessian phase amplitude x w v := by
    intro v w
    simp only [phaseRankOneHessian, ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_smul, mul_comm]
  apply ContinuousLinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w =>
      change actualHessianLift (phaseRankOneHessian phase amplitude x)
          (symmetricSquareProduct E v w) =
        incidenceLegalTensor (fderiv ℝ phase x) (amplitude x) (symmetricSquareProduct E v w)
      rw [actualHessianLift_product_of_symmetric _ hsym]
      change (fderiv ℝ phase x v) • ((fderiv ℝ phase x w) • amplitude x) =
        supportedRankLegalVariation (fderiv ℝ phase x).toLinearMap (amplitude x)
          (symmetricSquareProduct E v w)
      rw [supportedRankLegalVariation_product, smul_smul]
      rfl
    | add a b ha hb =>
      have hmk := (symmetricSquareQuotient E).map_add a b
      change Submodule.Quotient.mk (a + b) =
        (Submodule.Quotient.mk a : SymmetricSquare E) + Submodule.Quotient.mk b at hmk
      rw [hmk, map_add, map_add, ha, hb]

/-- The actual leading operator is linear in its normal value. -/
theorem incidenceLegalTensor_smul_normal (xi : E →L[ℝ] ℝ) (c : ℝ) (nu : V) :
    incidenceLegalTensor xi (c • nu) = c • incidenceLegalTensor xi nu := by
  apply ContinuousLinearMap.ext
  intro q
  change supportedRankCovectorSquare xi.toLinearMap q • (c • nu) =
    c • (supportedRankCovectorSquare xi.toLinearMap q • nu)
  exact smul_comm _ _ _

variable {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, E)

namespace LocalLegalWave

/-- The actual first-block Hessian principal tensor in any atlas source is
exactly the original legal tensor in that atlas's inverse tangent frame.
No differentiability of the phase outside the legal domain is assumed: its
cutoff-normal amplitude, and hence both tensors, vanish there. The existing
`atlasLeadingTensor_eq` theorem supplies this support-sensitive identity. -/
theorem actualHessianLift_phaseRankOneHessian_in_atlas
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (wave : LocalLegalWave F hF)
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
    (wave : LocalLegalWave F hF) (z : M) (frame : E →L[ℝ] E) :
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

end LocalLegalWave

#print axioms actualHessianLift_phaseRankOneHessian
#print axioms LocalLegalWave.actualHessianLift_phaseRankOneHessian_in_atlas
#print axioms LocalLegalWave.normalProjection_comp_tensor_in_frame

end GlobalEmbedding.Upgrade
