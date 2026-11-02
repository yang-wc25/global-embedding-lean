import Upgrade.CompactFixedAtlasJets
import GlobalEmbedding.Paper.TrueSecondFormChart
import GlobalEmbedding.Paper.SymmetricSquareMapProduct

/-!
# The fixed original atlas jets are the actual geometric jets

The differential range gives exactly the actual normal space. The projected
Hessian, on the original symmetric-square quotient, is exactly the ambient
true second form precomposed by the actual inverse chart differential. This
is the geometric dictionary required before applying two-jet stability.
-/

noncomputable section
open Set Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology TensorProduct

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual first fixed-coordinate jet is the actual immersion derivative
precomposed by the actual inverse chart differential. -/
theorem probeAtlasFirstJet_eq_mfderiv_frame
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    probeAtlasFirstJet A F i x =
      (mfderiv IM 𝓘(ℝ, V) F x).comp (probeAtlasFrame A i x) := by
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i)
    ((A.chart i).map_source hx)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (A.chart i x)
    ((hF ((A.chart i).symm (A.chart i x))).mdifferentiableAt (by simp)) hi
  rw [mfderiv_eq_fderiv, (A.chart i).left_inv hx] at hcomp
  exact hcomp

/-- The fixed-coordinate first jet is injective whenever the original actual
immersion derivative is injective. -/
theorem probeAtlasFirstJet_injective
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (himm : Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) :
    Function.Injective (probeAtlasFirstJet A F i x) := by
  rw [probeAtlasFirstJet_eq_mfderiv_frame A hA F hF i x hx,
    ← probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i x hx]
  exact himm.comp (probeAtlasInverseFrameEquiv A hA i x hx).injective

/-- The range of the fixed coordinate derivative gives the actual normal
space, with no separately selected normal frame. -/
theorem normalSpace_eq_probeAtlasFirstJet_range
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    normalSpace (I := IM) F x = (probeAtlasFirstJet A F i x).rangeᗮ := by
  rw [probeAtlasFirstJet_eq_mfderiv_frame A hA F hF i x hx,
    ← probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i x hx]
  have hr : ((mfderiv IM 𝓘(ℝ, V) F x).comp
      (probeAtlasInverseFrameEquiv A hA i x hx).toContinuousLinearMap).range =
      (mfderiv IM 𝓘(ℝ, V) F x).range :=
    LinearMap.range_comp_of_range_eq_top _
      (probeAtlasInverseFrameEquiv A hA i x hx).toLinearEquiv.range
  exact (congrArg (fun U : Submodule ℝ V ↦ Uᗮ) hr).symm

/-- The projected actual fixed-coordinate Hessian. -/
def probeAtlasProjectedSecondForm (A : BufferedAtlas M E) (F : M → V)
    (i : Fin A.count) (x : M) : SymmetricSquare E →L[ℝ] V :=
  (probeAtlasFirstJet A F i x).rangeᗮ.starProjection.comp (probeAtlasSecondJet A F i x)

/-- Exact fixed-chart formula for the original actual second fundamental
form. Source frame variation is explicitly retained. -/
theorem probeAtlasProjectedSecondForm_eq_trueSecondForm
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) :
    probeAtlasProjectedSecondForm A F i x =
      (normalSpace (I := IM) F x).subtypeL.comp
        ((LinearMap.toContinuousLinearMap
          (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)).comp
            (LinearMap.toContinuousLinearMap
              (symmetricSquareLinearMap (probeAtlasFrame A i x).toLinearMap))) := by
  have hcoord (v : E) :
      mfderiv IM IM (A.chart i) x (probeAtlasFrame A i x v) = v := by
    exact ((probeAtlasChart_mdifferentiable A hA i).mfderiv hx).apply_symm_apply v
  have hFc : ContDiffAt ℝ 2 (F ∘ (A.chart i).symm) (A.chart i x) :=
    ((probeAtlas_fixed_coordinate_smooth A hA F hF i).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hx))).of_le (by simp)
  have hproduct (v w : E) :
      symmetricSquareLinearMap (probeAtlasFrame A i x).toLinearMap
          (symmetricSquareProduct E v w) =
        symmetricSquareProduct E (probeAtlasFrame A i x v) (probeAtlasFrame A i x w) := by
    rw [symmetric_square_linear_map_eq]
    exact symmetricSquareMapL_product (probeAtlasFrame A i x) v w
  have hchart (v w : E) := trueSecondForm_chart F hF x (A.chart i)
    (IsManifold.maximalAtlas_subset_of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞) (hA.chart_mem i))
    hx (probeAtlasFrame A i x v) (probeAtlasFrame A i x w)
  have hchart' (v w : E) :
      (normalSpace (I := IM) F x).orthogonalProjectionOnto
        (fderiv ℝ (fderiv ℝ (F ∘ (A.chart i).symm)) (A.chart i x) v w) =
        trueSecondForm F hF x (symmetricSquareProduct E
          (probeAtlasFrame A i x v) (probeAtlasFrame A i x w)) := by
    have h := hchart v w
    change (normalSpace (I := IM) F x).orthogonalProjectionOnto
      (fderiv ℝ (fderiv ℝ (F ∘ (A.chart i).symm)) (A.chart i x)
        (mfderiv IM IM (A.chart i) x (probeAtlasFrame A i x v))
        (mfderiv IM IM (A.chart i) x (probeAtlasFrame A i x w))) = _ at h
    rwa [hcoord, hcoord] at h
  have hproj : (probeAtlasFirstJet A F i x).rangeᗮ.starProjection =
      (normalSpace (I := IM) F x).starProjection := by
    congr 1
    exact (normalSpace_eq_probeAtlasFirstJet_range A hA F hF i x hx).symm
  apply ContinuousLinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w =>
      change (probeAtlasFirstJet A F i x).rangeᗮ.starProjection
        (coordinateHessianJet (F ∘ (A.chart i).symm) (A.chart i x)
          (symmetricSquareProduct E v w)) =
        (trueSecondForm F hF x (symmetricSquareLinearMap
          (probeAtlasFrame A i x).toLinearMap (symmetricSquareProduct E v w)) : V)
      rw [hproj, coordinateHessianJet_product hFc, hproduct]
      exact congrArg (fun z : normalSpace (I := IM) F x ↦ (z : V)) (hchart' v w)
    | add a b ha hb =>
      change (probeAtlasProjectedSecondForm A F i x) (symmetricSquareQuotient E (a + b)) =
        ((normalSpace (I := IM) F x).subtypeL.comp
          ((LinearMap.toContinuousLinearMap
            (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)).comp
              (LinearMap.toContinuousLinearMap
                (symmetricSquareLinearMap (probeAtlasFrame A i x).toLinearMap))))
                  (symmetricSquareQuotient E (a + b))
      simp only [map_add]
      exact congrArg₂ (· + ·) ha hb

end GlobalEmbedding.Upgrade
