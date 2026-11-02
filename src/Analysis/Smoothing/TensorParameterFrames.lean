import Smoothing.TensorNativeTransitions
import Smoothing.ParameterProductAtlas

/-!
# Actual source-tangent tensor frames over nonzero parameter manifolds

The bundle fiber over (p,x) is the original source tangent space at x.
Joint convolution takes place in the genuine parameter/source product atlas.
The moving-frame coefficients are the spatial block of the genuine joint
chart Jacobian, so their full joint derivatives are supplied by the original
joint transition bounds with exactly one extra derivative.
-/

open Module Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

/-- The actual source tangent basis at the actual source point, with the
original source chart selected from the genuine product index. -/
def parameterTensorNativeFrame
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (i : Fin (parameterProductAtlas A B).count) (z : P × M) :
    Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) z.2) :=
  bufferedNativeTensorFrame A hA (parameterProductIndex A B i).2 z.2

/-- Parameter directions never enter the tangent slots of the tensor. -/
theorem parameterTensorNativeFrameTransition_eq_source
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (p i : Fin (parameterProductAtlas A B).count) (a r : Fin n)
    (y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) :
    tensorFrameTransition (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA) p i a r y =
      tensorFrameTransition A (bufferedNativeTensorFrame A hA)
        (parameterProductIndex A B p).2 (parameterProductIndex A B i).2 a r y.2 := rfl

/-- One spatial entry of the full parameter/source Jacobian. -/
def parameterTensorJacobianEntryCLM (a r : Fin n) :
    ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))) →L[ℝ] ℝ :=
  (((ContinuousLinearMap.proj r).comp (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap).comp
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      (0, EuclideanSpace.single a 1))

@[simp] theorem parameterTensorJacobianEntryCLM_apply (a r : Fin n)
    (L : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))) :
    parameterTensorJacobianEntryCLM a r L = (L (0, EuclideanSpace.single a 1)).2 r := rfl

theorem parameterTensorJacobianEntryCLM_norm_le (a r : Fin n) :
    ‖parameterTensorJacobianEntryCLM (d := d) a r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  rw [parameterTensorJacobianEntryCLM_apply, one_mul]
  apply (PiLp.norm_apply_le (L (0, EuclideanSpace.single a 1)).2 r).trans
  apply (norm_snd_le (L (0, EuclideanSpace.single a 1))).trans
  simpa using L.le_opNorm (0, EuclideanSpace.single a 1)

/-- The genuine frame change is exactly the source block of the genuine
joint chart derivative on each actual product overlap. -/
theorem parameterTensorNativeFrameTransition_eq_fderiv
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (p i : Fin (parameterProductAtlas A B).count) (a r : Fin n)
    {y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ bufferedChartOverlap (parameterProductAtlas A B) p i) :
    tensorFrameTransition (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA) p i a r y =
      parameterTensorJacobianEntryCLM a r
        (fderiv ℝ ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y) := by
  let pp := (parameterProductIndex A B p).1
  let ps := (parameterProductIndex A B p).2
  let ip := (parameterProductIndex A B i).1
  let is := (parameterProductIndex A B i).2
  have hyp : y.1 ∈ bufferedChartOverlap B pp ip := ⟨hy.1.1, hy.2.1⟩
  have hys : y.2 ∈ bufferedChartOverlap A ps is := ⟨hy.1.2, hy.2.2⟩
  rw [parameterTensorNativeFrameTransition_eq_source,
    tensorNativeFrameTransition_eq_fderiv A hA ps is a r hys]
  have hp := ((bufferedTransition_contDiffOn B hB pp ip).contDiffAt
    ((bufferedChartOverlap_open B pp ip).mem_nhds hyp)).differentiableAt (by simp)
  have hs := ((bufferedTransition_contDiffOn A hA ps is).contDiffAt
    ((bufferedChartOverlap_open A ps is).mem_nhds hys)).differentiableAt (by simp)
  have hprod := ((hp.hasFDerivAt.comp y hasFDerivAt_fst).prodMk
    (hs.hasFDerivAt.comp y hasFDerivAt_snd)).fderiv
  simp only [Function.comp_apply] at hprod
  change _ = parameterTensorJacobianEntryCLM a r
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
      (B.chart ip ((B.chart pp).symm z.1), A.chart is ((A.chart ps).symm z.2))) y)
  rw [hprod]
  rfl

/-- Joint smoothness of the actual frame coefficients is supplied by the
actual product atlas, even for positive parameter dimension. -/
theorem parameterTensorNativeFrameTransition_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (p i : Fin (parameterProductAtlas A B).count) (a r : Fin n) :
    ContDiffOn ℝ ∞
      (tensorFrameTransition (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA) p i a r)
      (bufferedChartOverlap (parameterProductAtlas A B) p i) := by
  have hder := (bufferedTransition_contDiffOn (parameterProductAtlas A B)
    (parameterProductAtlas_smooth A B hA hB) p i).fderiv_of_isOpen
      (bufferedChartOverlap_open (parameterProductAtlas A B) p i) (m := ∞) (by simp)
  apply ((parameterTensorJacobianEntryCLM a r).contDiff.comp_contDiffOn hder).congr
  intro y hy
  exact parameterTensorNativeFrameTransition_eq_fderiv A B hA hB p i a r hy

/-- No extra frame-derivative provider: the next total joint transition jet
bounds the current total joint frame-coefficient jet. -/
theorem parameterTensorNativeFrameTransition_jet_le
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (p i : Fin (parameterProductAtlas A B).count) (a r : Fin n)
    {y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ bufferedChartOverlap (parameterProductAtlas A B) p i) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (tensorFrameTransition (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA) p i a r) y‖ ≤
      ‖iteratedFDeriv ℝ (k + 1)
        ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ := by
  have hder := (bufferedTransition_contDiffOn (parameterProductAtlas A B)
    (parameterProductAtlas_smooth A B hA hB) p i).fderiv_of_isOpen
      (bufferedChartOverlap_open (parameterProductAtlas A B) p i) (m := ∞) (by simp)
  have heq : tensorFrameTransition (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA) p i a r =ᶠ[𝓝 y]
      parameterTensorJacobianEntryCLM a r ∘ fderiv ℝ
        ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) := by
    filter_upwards [(bufferedChartOverlap_open (parameterProductAtlas A B) p i).mem_nhds hy] with z hz
    exact parameterTensorNativeFrameTransition_eq_fderiv A B hA hB p i a r hz
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  rw [(parameterTensorJacobianEntryCLM a r).iteratedFDeriv_comp_left
    (hder.contDiffAt ((bufferedChartOverlap_open (parameterProductAtlas A B) p i).mem_nhds hy)) (by simp)]
  apply ((parameterTensorJacobianEntryCLM a r).norm_compContinuousMultilinearMap_le _).trans
  rw [← norm_iteratedFDeriv_fderiv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (parameterTensorJacobianEntryCLM_norm_le a r)
    (norm_nonneg (iteratedFDeriv ℝ k (fderiv ℝ
      ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm)) y))

end

end GlobalEmbedding.Offline
