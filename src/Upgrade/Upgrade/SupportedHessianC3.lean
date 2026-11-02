import Upgrade.RankQProbeResponse
import Upgrade.CompactFixedAtlasJets
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Actual Hessian C³ estimates for fixed-normal incidence coordinates

These are derivative estimates of literal coordinate Hessians and operator
compositions. The original Hessian lift and native atlas derivative bounds
are reused. A derivative of the normal-identification operator is retained
explicitly, rather than inferred from its pointwise orthogonality.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

section OperatorDerivative
variable {X S Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- The derivative of the actual identification-times-Hessian expression
contains both the identification derivative and the true Hessian derivative. -/
theorem norm_fderiv_identified_hessian_product_le
    (Q : X → Z →L[ℝ] Z) (H : X → S →L[ℝ] Z) (x : X)
    (hQ : DifferentiableAt ℝ Q x) (hH : DifferentiableAt ℝ H x) :
    ‖fderiv ℝ (fun z ↦ (Q z).comp (H z)) x‖ ≤
      ‖fderiv ℝ Q x‖ * ‖H x‖ + ‖Q x‖ * ‖fderiv ℝ H x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  rw [fderiv_clm_comp hQ hH]
  change ‖(Q x).comp (fderiv ℝ H x d) + (fderiv ℝ Q x d).comp (H x)‖ ≤ _
  calc
    _ ≤ ‖(Q x).comp (fderiv ℝ H x d)‖ + ‖(fderiv ℝ Q x d).comp (H x)‖ := norm_add_le _ _
    _ ≤ ‖Q x‖ * ‖fderiv ℝ H x d‖ + ‖fderiv ℝ Q x d‖ * ‖H x‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖Q x‖ * (‖fderiv ℝ H x‖ * ‖d‖) + (‖fderiv ℝ Q x‖ * ‖d‖) * ‖H x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left ((fderiv ℝ H x).le_opNorm d) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right ((fderiv ℝ Q x).le_opNorm d) (norm_nonneg _))
    _ = _ := by ring

/-- Fixed source transport and a fixed norm-one normal-coordinate map
preserve the native derivative bound with the exact right-transport factor. -/
theorem norm_fderiv_fixed_left_right_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (J : Z →L[ℝ] W) (hJ : ‖J‖ ≤ 1)
    (C : X → S →L[ℝ] Z) (x : X) (hC : DifferentiableAt ℝ C x)
    (K : S →L[ℝ] S) :
    ‖fderiv ℝ (fun z ↦ J.comp ((C z).comp K)) x‖ ≤
      ‖fderiv ℝ C x‖ * ‖K‖ := by
  have hR : DifferentiableAt ℝ (fun z ↦ (C z).comp K) x :=
    hC.clm_comp (differentiableAt_const K)
  apply ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (fun z ↦ J.comp ((C z).comp K)) x)
    (mul_nonneg (norm_nonneg (fderiv ℝ C x)) (norm_nonneg K))
  intro d
  rw [fderiv_fixed_tensor_left_transport _ hR J d,
    fderiv_fixed_tensor_right_transport C hC K d]
  calc
    ‖J.comp ((fderiv ℝ C x d).comp K)‖ ≤ ‖J‖ * ‖(fderiv ℝ C x d).comp K‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖(fderiv ℝ C x d).comp K‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ ≤ ‖fderiv ℝ C x d‖ * ‖K‖ := by
      simpa only [one_mul] using ContinuousLinearMap.opNorm_comp_le (fderiv ℝ C x d) K
    _ ≤ (‖fderiv ℝ C x‖ * ‖d‖) * ‖K‖ :=
      mul_le_mul_of_nonneg_right ((fderiv ℝ C x).le_opNorm d) (norm_nonneg K)
    _ = _ := by ring

end OperatorDerivative

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section ActualHessian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The actual descended Hessian is controlled by the native second jet in
the original quotient norm, with the accepted lift's exact norm constant. -/
theorem coordinateHessianJet_norm_le_native_second (f : E → F) (x : E) :
    ‖coordinateHessianJet f x‖ ≤ actualHessianLiftConstant E F * ‖iteratedFDeriv ℝ 2 f x‖ := by
  have h := actualHessianLift_sub_norm_le (fderiv ℝ (fderiv ℝ f) x) 0
  simp only [map_zero, sub_zero] at h
  rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv] at h
  exact h

/-- The derivative of the literal descended Hessian is the fixed Hessian
lift of the actual third derivative; no independent second-form estimate is
introduced. -/
theorem coordinateHessianJet_fderiv_norm_le_native_third
    (f : E → F) (x : E) (hf : ContDiffAt ℝ ∞ f x) :
    ‖fderiv ℝ (coordinateHessianJet f) x‖ ≤
      actualHessianLiftConstant E F * ‖iteratedFDeriv ℝ 3 f x‖ := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hDD : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) x := hD.fderiv_right (by simp)
  have hd : fderiv ℝ (coordinateHessianJet f) x =
      (actualHessianLift (E := E) (F := F)).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) :=
    ((actualHessianLift (E := E) (F := F)).hasFDerivAt.comp x
      (hDD.differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [hd]
  have h := ContinuousLinearMap.opNorm_comp_le (actualHessianLift (E := E) (F := F))
    (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x)
  rw [← norm_iteratedFDeriv_one (fderiv ℝ (fderiv ℝ f)),
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv] at h
  exact h

end ActualHessian

#print axioms norm_fderiv_identified_hessian_product_le
#print axioms norm_fderiv_fixed_left_right_le
#print axioms coordinateHessianJet_norm_le_native_second
#print axioms coordinateHessianJet_fderiv_norm_le_native_third

end GlobalEmbedding.Upgrade
