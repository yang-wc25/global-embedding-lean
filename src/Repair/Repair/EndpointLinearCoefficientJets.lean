import Repair.EndpointLinearCoordinateFormula

/-! Uniform all-order bounds of the original template coordinate coefficients.
The receiving Jacobian is the only variable input. The coefficient map is the
same fixed template map, and the quadratic tensor transformation is explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology TensorProduct BigOperators
namespace GlobalEmbedding.Continuation
variable {n : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Dual" => D →L[ℝ] ℝ
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance repairCoefficientDualNormed : NormedAddCommGroup Dual := inferInstance
private local instance repairCoefficientDualSpace : NormedSpace ℝ Dual := inferInstance
private local instance repairCoefficientTensorNormed : NormedAddCommGroup Tensor := inferInstance
private local instance repairCoefficientTensorSpace : NormedSpace ℝ Tensor := inferInstance

def repairJacobianRow (r : Fin n) : (D →L[ℝ] D) →L[ℝ] Dual :=
  (ContinuousLinearMap.compL ℝ D D ℝ) (EuclideanSpace.proj r)

theorem repairJacobianRow_norm (r : Fin n) : ‖repairJacobianRow r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro R
  change ‖(EuclideanSpace.proj r).comp R‖ ≤ 1 * ‖R‖
  have hproj : ‖(EuclideanSpace.proj r : D →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖v r‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact PiLp.norm_apply_le v r
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      hproj (norm_nonneg R))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem repair_symmetric_jacobian_tensor_smooth
    (R : X → D →L[ℝ] D) (O : Set X) (hR : ContDiffOn ℝ ∞ R O)
    (r s : Fin n) :
    ContDiffOn ℝ ∞ (fun x => repairSymmetricJacobianTensor (R x) r s) O := by
  let L := ContinuousLinearMap.smulRightL ℝ D Dual
  have hr : ContDiffOn ℝ ∞ (fun x => repairJacobianRow r (R x)) O :=
    (repairJacobianRow r).contDiff.comp_contDiffOn hR
  have hs : ContDiffOn ℝ ∞ (fun x => repairJacobianRow s (R x)) O :=
    (repairJacobianRow s).contDiff.comp_contDiffOn hR
  exact ((L.contDiff.comp_contDiffOn hr).clm_apply hs |>.add
    ((L.contDiff.comp_contDiffOn hs).clm_apply hr)).const_smul (1/2 : ℝ)

/-- A j-jet of the actual quadratic Jacobian tensor reads only the j-jet
prefix of that same Jacobian. The factor is independent of chart count. -/
theorem repair_symmetric_jacobian_tensor_scaled_jet
    (R : X → D →L[ℝ] D) (O : Set X) (hO : IsOpen O)
    (hR : ContDiffOn ℝ ∞ R O) (r s : Fin n)
    (j : ℕ) (ell M : ℝ) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (x : X) (hx : x ∈ O)
    (hJets : ∀ k ≤ j, ell^k * ‖iteratedFDeriv ℝ k R x‖ ≤ M) :
    ell^j * ‖iteratedFDeriv ℝ j
      (fun y => repairSymmetricJacobianTensor (R y) r s) x‖ ≤ 2^j*M^2 := by
  let L := ContinuousLinearMap.smulRightL ℝ D Dual
  let row := fun a y => repairJacobianRow a (R y)
  have hrow (a : Fin n) : ContDiffOn ℝ ∞ (row a) O :=
    (repairJacobianRow a).contDiff.comp_contDiffOn hR
  have hrowJet (a : Fin n) (k : ℕ) (hk : k ≤ j) :
      ell^k * ‖iteratedFDeriv ℝ k (row a) x‖ ≤ M := by
    have h := (repairJacobianRow a).norm_iteratedFDeriv_comp_left
      (hR.contDiffAt (hO.mem_nhds hx)) (n := k) (by simp)
    calc
      _ ≤ ell^k * (‖repairJacobianRow a‖ * ‖iteratedFDeriv ℝ k R x‖) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hell _)
      _ ≤ ell^k * (1 * ‖iteratedFDeriv ℝ k R x‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (repairJacobianRow_norm a) (norm_nonneg _))
          (pow_nonneg hell _)
      _ ≤ M := by simpa only [one_mul] using hJets k hk
  have hp (a b : Fin n) := slow_bilinear_jet_bound L
    (ContinuousLinearMap.norm_smulRightL_le (𝕜 := ℝ) (E := D) (Fₗ := Dual))
    O hO (row a) (row b) (hrow a) (hrow b) j ell M M hell hM x hx
    (hrowJet a) (hrowJet b)
  let f := fun y => L (row r y) (row s y)
  let g := fun y => L (row s y) (row r y)
  have hf : ContDiffOn ℝ ∞ f O := (L.contDiff.comp_contDiffOn (hrow r)).clm_apply (hrow s)
  have hg : ContDiffOn ℝ ∞ g O := (L.contDiff.comp_contDiffOn (hrow s)).clm_apply (hrow r)
  change ell^j * ‖iteratedFDeriv ℝ j (fun y => (1/2 : ℝ) • (f y + g y)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    ((hf.add hg).contDiffAt (hO.mem_nhds hx) |>.of_le (by simp)), norm_smul]
  rw [fun_iteratedFDeriv_add_apply (hf.contDiffAt (hO.mem_nhds hx) |>.of_le (by simp))
    (hg.contDiffAt (hO.mem_nhds hx) |>.of_le (by simp))]
  have hnorm := norm_add_le (iteratedFDeriv ℝ j f x) (iteratedFDeriv ℝ j g x)
  have hscale := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hell j)
  have hfg := hp r s
  have hgf := hp s r
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at *
  dsimp only [f,g] at *
  nlinarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_symmetric_jacobian_tensor_scaled_jet

