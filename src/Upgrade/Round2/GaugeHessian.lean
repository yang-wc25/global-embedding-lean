import Round2.GaugeProduct
import Upgrade.SupportedProbeC3

/-!
# Actual Hessian source bounds after zero-locus gauge cancellation

The Hessian is the existing descended native second derivative.  Its source
normalization is fixed at the prepared center, and no derivative of a chosen
normal identification is estimated.  The first-jet left inverse is supplied
as a geometric splitting, with its quantitative bound stated separately.
-/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {E V W Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private noncomputable local instance gaugeHessianNorm :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance gaugeHessianSpace :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance gaugeTargetFormNorm :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance gaugeTargetFormSpace :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] W) := ContinuousLinearMap.toNormedSpace

/-- The literal native Hessian with the already fixed center normalization. -/
def gaugeNormalizedHessian (f : E → V)
    (Ksource : SymmetricSquare E →L[ℝ] SymmetricSquare E) (z : E) :
    SymmetricSquare E →L[ℝ] V := (coordinateHessianJet f z).comp Ksource

/-- The actual normalized Hessian derivative retains the fixed normalization
factor and is bounded by the actual third derivative of the same map. -/
theorem gaugeNormalizedHessian_derivative_bound
    (f : E → V) (Ksource : SymmetricSquare E →L[ℝ] SymmetricSquare E)
    (x : E) (hf : ContDiffAt ℝ ∞ f x) :
    ‖fderiv ℝ (gaugeNormalizedHessian f Ksource) x‖ ≤
      (actualHessianLiftConstant E V * ‖iteratedFDeriv ℝ 3 f x‖) * ‖Ksource‖ := by
  have hH := coordinateHessianJet_differentiableAt f x hf
  have hbase : ‖fderiv ℝ (gaugeNormalizedHessian f Ksource) x‖ ≤
      ‖fderiv ℝ (coordinateHessianJet f) x‖ * ‖Ksource‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro d
    rw [show fderiv ℝ (gaugeNormalizedHessian f Ksource) x d =
        (fderiv ℝ (coordinateHessianJet f) x d).comp Ksource from
      fderiv_fixed_tensor_right_transport (coordinateHessianJet f) hH Ksource d]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (coordinateHessianJet f) x).le_opNorm d)
        (by positivity) |>.trans_eq (by ring))
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (coordinateHessianJet_fderiv_norm_le_native_third f x hf) (by positivity))

/-- Bound for the actual composed source derivative at an incidence zero.
The gauge derivative can be arbitrarily large. Its tangent action is recovered
from `T·df=0`; the retained correction is quadratic in the native second jet. -/
theorem norm_incidence_hessian_derivative_without_gauge_bound
    (f : E → V) (T : E → V →L[ℝ] W)
    (Ksource : SymmetricSquare E →L[ℝ] SymmetricSquare E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hT : DifferentiableAt ℝ T x)
    (hTnorm : ‖T x‖ ≤ 1)
    (hTL : ∀ᶠ z in 𝓝 x, (T z).comp (fderiv ℝ f z) = 0)
    (R : W →L[ℝ] V) (K : V →L[ℝ] E)
    (hsplit : R.comp (T x) + (fderiv ℝ f x).comp K = ContinuousLinearMap.id ℝ V)
    (D : (SymmetricSquare E →L[ℝ] W) →L[ℝ] Y)
    (hD : ∀ A : W →L[ℝ] W,
      D (A.comp ((T x).comp (gaugeNormalizedHessian f Ksource x))) = 0)
    (B2 B3 Kbound : ℝ)
    (h2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ B2)
    (h3 : ‖iteratedFDeriv ℝ 3 f x‖ ≤ B3) (hK : ‖K‖ ≤ Kbound) :
    ‖D.comp (fderiv ℝ (fun z ↦ (T z).comp (gaugeNormalizedHessian f Ksource z)) x)‖ ≤
      ‖D‖ * (actualHessianLiftConstant E V * B3 +
        B2 * Kbound * (actualHessianLiftConstant E V * B2)) * ‖Ksource‖ := by
  have hLcont : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hL : DifferentiableAt ℝ (fderiv ℝ f) x := hLcont.differentiableAt (by simp)
  have hH : DifferentiableAt ℝ (gaugeNormalizedHessian f Ksource) x :=
    (coordinateHessianJet_differentiableAt f x hf).clm_comp (differentiableAt_const Ksource)
  have hraw := norm_incidence_derivative_without_gauge_bound
    T (fderiv ℝ f) (gaugeNormalizedHessian f Ksource) x hT hL hH hTL R K hsplit D hD
  have hlift := actualHessianLiftConstant_nonneg («E» := E) (F := V)
  have h2pos : 0 ≤ B2 := (norm_nonneg _).trans h2
  have h3pos : 0 ≤ B3 := (norm_nonneg _).trans h3
  have hKpos : 0 ≤ Kbound := K.opNorm_nonneg.trans hK
  have hDL : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2 := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
    exact h2
  have hDH : ‖fderiv ℝ (gaugeNormalizedHessian f Ksource) x‖ ≤
      (actualHessianLiftConstant E V * B3) * ‖Ksource‖ :=
    (gaugeNormalizedHessian_derivative_bound f Ksource x hf).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hlift) (by positivity))
  have hHnorm : ‖gaugeNormalizedHessian f Ksource x‖ ≤
      (actualHessianLiftConstant E V * B2) * ‖Ksource‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ((coordinateHessianJet_norm_le_native_second f x).trans
        (mul_le_mul_of_nonneg_left h2 hlift)) (by positivity))
  apply hraw.trans
  calc
    _ ≤ ‖D‖ * 1 * ((actualHessianLiftConstant E V * B3) * ‖Ksource‖ +
        B2 * Kbound * ((actualHessianLiftConstant E V * B2) * ‖Ksource‖)) := by
      gcongr
    _ = _ := by ring

#print axioms gaugeNormalizedHessian_derivative_bound
#print axioms norm_incidence_hessian_derivative_without_gauge_bound

end GlobalEmbedding.Upgrade
