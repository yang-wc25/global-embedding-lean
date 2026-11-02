import Repair.EndpointLinearCoefficientJets
import Repair.EndpointJacobianProfiles
import Smoothing.ParameterRound2MeanTensorAlgebra

/-! The original ordered symmetric coefficient vector has the same maximum
norm as its scalar coordinates.  The bound uses the selected fixed template
and the genuine observer/owner transition, with no chart-count factor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {n N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance coefficientProfileTensorNormed : NormedAddCommGroup Tensor := inferInstance
private local instance coefficientProfileTensorSpace : NormedSpace ℝ Tensor := inferInstance

def repairTemplateCoordinateVector (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1)) (R : D →L[ℝ] D) : Fin (n*n) → ℝ :=
  fun k => template.coefficients
    (repairSymmetricJacobianTensor R (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) a

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem repair_template_coordinate_vector_smooth
    (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1))
    (R : X → D →L[ℝ] D) (O : Set X) (hR : ContDiffOn ℝ ∞ R O) :
    ContDiffOn ℝ ∞ (fun y => repairTemplateCoordinateVector template a (R y)) O := by
  apply contDiffOn_pi.2
  intro k
  exact (((ContinuousLinearMap.proj a).comp template.coefficients).contDiff.comp_contDiffOn
    (repair_symmetric_jacobian_tensor_smooth R O hR
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))

theorem repair_template_coordinate_vector_scaled_jet
    (template : ActualGoodDictionaryTemplate D V)
    (a : EdgePair (Module.finrank ℝ D+1)) (A : ℝ) (hA : 0 ≤ A)
    (hCoeff : ‖template.coefficients‖ ≤ A)
    (R : X → D →L[ℝ] D) (O : Set X) (hO : IsOpen O)
    (hR : ContDiffOn ℝ ∞ R O) (j : ℕ) (ell M : ℝ)
    (hell : 0 < ell) (hM : 0 ≤ M) (x : X) (hx : x ∈ O)
    (hJets : ∀ k ≤ j, ell^k * ‖iteratedFDeriv ℝ k R x‖ ≤ M) :
    ell^j * ‖iteratedFDeriv ℝ j
      (fun y => repairTemplateCoordinateVector template a (R y)) x‖ ≤ A*(2^j*M^2) := by
  have hs := repair_template_coordinate_vector_smooth template a R O hR
  apply parameterRound2_joint_pi_weighted_jet _ x
    (hs.contDiffAt (hO.mem_nhds hx)) j ell (A*(2^j*M^2)) hell (by positivity)
  intro k
  let L : Tensor →L[ℝ] ℝ := (ContinuousLinearMap.proj a).comp template.coefficients
  have hL : ‖L‖ ≤ A := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro Q
    exact (norm_le_pi_norm (template.coefficients Q) a).trans
      ((template.coefficients.le_opNorm Q).trans
        (mul_le_mul_of_nonneg_right hCoeff (norm_nonneg Q)))
  have hTensor := repair_symmetric_jacobian_tensor_scaled_jet R O hO hR
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 j ell M hell.le hM x hx hJets
  have h := increments_fixed_linear_coefficient_scaled_jet L O hO
    (fun y => repairSymmetricJacobianTensor (R y)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (repair_symmetric_jacobian_tensor_smooth R O hR _ _) j ell (2^j*M^2) hell.le hx hTensor
  exact h.trans (mul_le_mul_of_nonneg_right hL (by positivity))

def repairOriginalLinearProfile (A : ℝ) (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  A * (2^j * (∑ k ∈ Finset.range (j+1), repairTransitionJacobianProfile T k)^2)

theorem repairOriginalLinearProfile_prefix (A : ℝ) (T U : ℕ → ℝ) (j : ℕ)
    (h : ∀ k ≤ j+1, T k = U k) :
    repairOriginalLinearProfile A T j = repairOriginalLinearProfile A U j := by
  unfold repairOriginalLinearProfile
  congr 2
  apply congrArg (fun t : ℝ => t^2)
  apply Finset.sum_congr rfl
  intro k hk
  exact repairTransitionJacobianProfile_prefix T U k
    (fun l hl => h l (by have := Finset.mem_range.mp hk; omega))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_template_coordinate_vector_scaled_jet
#print axioms GlobalEmbedding.Continuation.repairOriginalLinearProfile_prefix
