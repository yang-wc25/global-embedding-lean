import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Actual complexification of finite-coordinate real multilinear coefficients

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The local real-analytic extension requires actual complex Taylor
coefficients, their real-input agreement and a geometric degree-dependent norm bound.
-/

namespace GlobalEmbedding.Paper

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

/-- Complexify a real multilinear coefficient by its actual values on the standard real basis.
Each coordinate monomial is an actual continuous complex multilinear map; their finite sum
is the actual extension. The zero-dimensional and degree-zero cases use the same formula. -/
noncomputable def collarRealMultilinearComplexification {m n : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Fin m → ℝ) F) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ Fin m → ℂ) F :=
  ∑ σ : Fin n → Fin m,
    ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
      (fun i ↦ ContinuousLinearMap.proj (σ i))).smulRight
      (p (fun i ↦ Pi.single (σ i) 1))

omit [IsScalarTower ℝ ℂ F] in
/-- The actual extension is the standard complex coordinate monomial expansion. -/
theorem collar_real_multilinear_complexification_apply {m n : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Fin m → ℝ) F)
    (v : Fin n → Fin m → ℂ) :
    collarRealMultilinearComplexification p v =
      ∑ σ : Fin n → Fin m, (∏ i : Fin n, v i (σ i)) •
        p (fun i ↦ Pi.single (σ i) 1) := by
  simp [collarRealMultilinearComplexification]

/-- Actual agreement on every real tuple follows from the full finite-basis expansion of p.
Expand every input in standard basis vectors, use multilinearity of p, then identify complex
scalar multiplication by real scalars through the scalar tower. No extension is postulated. -/
theorem collar_real_multilinear_complexification_real {m n : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Fin m → ℝ) F)
    (v : Fin n → Fin m → ℝ) :
    collarRealMultilinearComplexification p (fun i j ↦ (v i j : ℂ)) = p v := by
  classical
  have hv : (fun i ↦ ∑ j : Fin m, v i j • (Pi.single j 1 : Fin m → ℝ)) = v := by
    funext i j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [collar_real_multilinear_complexification_apply]
  conv_rhs => rw [← hv]
  rw [p.map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [p.map_smul_univ]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_prod]
  rfl

omit [IsScalarTower ℝ ℂ F] in
/-- Complex coefficient operator norms grow at most exponentially with degree.
Each standard basis tuple has norm at most one, so its p-value has norm at most ‖p‖.
Each coordinate monomial is bounded by the product of input sup norms. Sum over m^n
coordinate choices and apply the multilinear operator-norm criterion. -/
theorem collar_real_multilinear_complexification_norm {m n : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Fin m → ℝ) F) :
    ‖collarRealMultilinearComplexification p‖ ≤ (m : ℝ) ^ n * ‖p‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [collar_real_multilinear_complexification_apply]
  calc
    _ ≤ ∑ σ : Fin n → Fin m,
        ‖(∏ i : Fin n, v i (σ i)) • p (fun i ↦ Pi.single (σ i) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Fin n → Fin m, (∏ i : Fin n, ‖v i‖) * ‖p‖ := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [norm_smul, norm_prod]
      apply mul_le_mul
      · apply Finset.prod_le_prod₀
        · intro i hi; positivity
        · intro i hi; exact norm_le_pi_norm (v i) (σ i)
      · simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using
          p.le_opNorm (fun i ↦ Pi.single (σ i) 1)
      · positivity
      · positivity
    _ = ((m : ℝ) ^ n * ‖p‖) * ∏ i : Fin n, ‖v i‖ := by
      simp [mul_comm, mul_left_comm]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarRealMultilinearComplexification
#print axioms GlobalEmbedding.Paper.collar_real_multilinear_complexification_real
#print axioms GlobalEmbedding.Paper.collar_real_multilinear_complexification_norm
