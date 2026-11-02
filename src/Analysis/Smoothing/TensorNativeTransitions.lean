import Smoothing.TensorNativeFrames
import Smoothing.TensorSmoothingRegularity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Native frame transitions are the genuine chart Jacobians

The extra tensor frame provider is derived from the original coordinate
transition provider, with exactly one extra derivative. Both frame factors
therefore use the uniform chart data of Setup 6; no independent matrix field
or hidden tensor-transition regularity is imposed.
-/

open Module Manifold IsManifold GlobalEmbedding.Paper Function Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- On the true overlap, the change of the actual tangent chart bases is
exactly the derivative of the actual chart transition. -/
theorem tensorNativeFrameTransition_eq_fderiv
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (p i : Fin A.count) (a r : Fin n)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ bufferedChartOverlap A p i) :
    tensorFrameTransition A (bufferedNativeTensorFrame A hA) p i a r y =
      (fderiv ℝ (A.chart i ∘ (A.chart p).symm) y (EuclideanSpace.single a 1)) r := by
  classical
  have hi : (A.chart p).symm y ∈ (A.chart i).source := A.inner_subset i hy.2
  unfold tensorFrameTransition
  rw [bufferedNativeTensorFrame_at_inverse A hA p y hy.1,
    bufferedSourceChartBasis_apply A hA p y hy.1]
  unfold bufferedNativeTensorFrame
  simp only [dite_eq_left hi, Basis.map_repr, LinearEquiv.trans_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  have hc := mfderiv_comp y ((bufferedChartMDifferentiable A hA i).mdifferentiableAt hi)
    ((bufferedChartMDifferentiable A hA p).mdifferentiableAt_symm hy.1)
  rw [mfderiv_eq_fderiv] at hc
  have hce := congrArg (fun L =>
    (L ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y).symm
      (EuclideanSpace.single a 1)) : EuclideanSpace ℝ (Fin n)) r) hc
  exact hce.symm

/-- Evaluation of one Jacobian entry is a genuine continuous linear map. -/
def tensorJacobianEntryCLM (a r : Fin n) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj r).comp (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single a 1))

@[simp] theorem tensorJacobianEntryCLM_apply (a r : Fin n)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    tensorJacobianEntryCLM a r L = (L (EuclideanSpace.single a 1)) r := rfl

/-- The Jacobian entry projection has norm at most one in the actual
Euclidean model, so no target dimension is hidden in its estimate. -/
theorem tensorJacobianEntryCLM_norm_le (a r : Fin n) : ‖tensorJacobianEntryCLM a r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  rw [tensorJacobianEntryCLM_apply, one_mul]
  apply (PiLp.norm_apply_le (L (EuclideanSpace.single a 1)) r).trans
  simpa using L.le_opNorm (EuclideanSpace.single a 1)

/-- Native Jacobian coefficients are smooth on the actual overlap. -/
theorem tensorNativeFrameTransition_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (p i : Fin A.count) (a r : Fin n) :
    ContDiffOn ℝ ∞ (tensorFrameTransition A (bufferedNativeTensorFrame A hA) p i a r)
      (bufferedChartOverlap A p i) := by
  have hder := (bufferedTransition_contDiffOn A hA p i).fderiv_of_isOpen
    (bufferedChartOverlap_open A p i) (m := ∞) (by simp)
  apply ((tensorJacobianEntryCLM a r).contDiff.comp_contDiffOn hder).congr
  intro y hy
  exact tensorNativeFrameTransition_eq_fderiv A hA p i a r hy

/-- Every derivative of the frame transition is bounded by the next genuine
chart-transition derivative, with no new geometric provider. -/
theorem tensorNativeFrameTransition_jet_le
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (p i : Fin A.count) (a r : Fin n)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ bufferedChartOverlap A p i) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (tensorFrameTransition A (bufferedNativeTensorFrame A hA) p i a r) y‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) (A.chart i ∘ (A.chart p).symm) y‖ := by
  have hder := (bufferedTransition_contDiffOn A hA p i).fderiv_of_isOpen
    (bufferedChartOverlap_open A p i) (m := ∞) (by simp)
  have heq : tensorFrameTransition A (bufferedNativeTensorFrame A hA) p i a r =ᶠ[𝓝 y]
      tensorJacobianEntryCLM a r ∘ fderiv ℝ (A.chart i ∘ (A.chart p).symm) := by
    filter_upwards [(bufferedChartOverlap_open A p i).mem_nhds hy] with z hz
    exact tensorNativeFrameTransition_eq_fderiv A hA p i a r hz
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  rw [(tensorJacobianEntryCLM a r).iteratedFDeriv_comp_left
    (hder.contDiffAt ((bufferedChartOverlap_open A p i).mem_nhds hy)) (by simp)]
  apply ((tensorJacobianEntryCLM a r).norm_compContinuousMultilinearMap_le _).trans
  rw [← norm_iteratedFDeriv_fderiv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (tensorJacobianEntryCLM_norm_le a r)
    (norm_nonneg (iteratedFDeriv ℝ k (fderiv ℝ (A.chart i ∘ (A.chart p).symm)) y))

end

end GlobalEmbedding.Offline
