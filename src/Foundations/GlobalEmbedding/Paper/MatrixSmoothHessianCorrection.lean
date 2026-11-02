import GlobalEmbedding.Paper.MatrixSmoothNewtonFamily

/-!
# Smooth corrections from a uniformly bounded Hessian

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
lines 311–315. DAG node: `matrix-smooth-hessian-correction`.
-/

open Set Metric
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A smooth nonlinear equation with bounded vertical Hessian, bounded inverse linearization
at zero and small residual has a unique smooth small zero family, with quantitative bounds.

Proof: apply the mean value inequality to the vertical derivative on the convex coefficient
ball. Its change from the derivative at zero has norm at most `K * r`. The inverse derivative
bound makes the normalized Newton defect at most `L * K * r ≤ 1/4`; the actual normalized
residual is at most `L * ε ≤ r/2`. The smooth Newton family theorem gives a smooth solution,
its strict interior bound and uniqueness. Its actual residual estimate gives the bound
`(4/3) * L * ε`. Source: `prop:matrix` proof, lines 311–315. -/
theorem smooth_hessian_small_residual_correction
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (U : Set P) (hU : IsOpen U) (f : P → X → X) (A : P → X ≃L[ℝ] X)
    (r L K ε : ℝ) (hr : 0 < r) (hL : 0 < L) (hK : 0 ≤ K) (_hε : 0 ≤ ε)
    (hsmall : 4 * L * K * r ≤ 1) (hresSmall : L * ε ≤ r / 2)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (hA : ∀ p ∈ U, (A p : X →L[ℝ] X) = fderiv ℝ (f p) 0)
    (hAinv : ∀ p ∈ U, ‖(A p).symm.toContinuousLinearMap‖ ≤ L)
    (hHess : ∀ p ∈ U, ∀ x ∈ closedBall (0 : X) r,
      ‖fderiv ℝ (fderiv ℝ (f p)) x‖ ≤ K)
    (hres : ∀ p ∈ U, ‖f p 0‖ ≤ ε) :
    ∃ c : P → X, ContDiffOn ℝ ∞ c U ∧
      (∀ p ∈ U, f p (c p) = 0 ∧
        ‖c p‖ ≤ (4 / 3 : ℝ) * L * ε ∧ ‖c p‖ ≤ 2 * r / 3 ∧
        (∀ y : X, ‖y‖ ≤ r → f p y = 0 → y = c p)) ∧
      (∀ p ∈ U, ∀ q ∈ U, (∀ x, f p x = f q x) → c p = c q) := by
  have hsmooth (p : P) (hp : p ∈ U) : ContDiff ℝ ∞ (f p) := by
    exact hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x ↦ ⟨hp, mem_univ x⟩)
  have hD (p : P) (hp : p ∈ U) (x : X) (hx : x ∈ closedBall (0 : X) r) :
      ‖ContinuousLinearMap.id ℝ X - (A p).symm.toContinuousLinearMap.comp
        (fderiv ℝ (f p) x)‖ ≤ 1 / 4 := by
    have hderivDiff : Differentiable ℝ (fderiv ℝ (f p)) := by
      exact ((contDiff_infty_iff_fderiv.1 (hsmooth p hp)).2).differentiable (by simp)
    have hzero : (0 : X) ∈ closedBall (0 : X) r := by simp [hr.le]
    have hbound : ‖fderiv ℝ (f p) x - fderiv ℝ (f p) 0‖ ≤ K * ‖x‖ := by
      simpa using (convex_closedBall (0 : X) r).norm_image_sub_le_of_norm_fderiv_le
        (fun y _ ↦ hderivDiff y) (hHess p hp) hzero hx
    have hid : ContinuousLinearMap.id ℝ X - (A p).symm.toContinuousLinearMap.comp
        (fderiv ℝ (f p) x) = (A p).symm.toContinuousLinearMap.comp
        ((A p : X →L[ℝ] X) - fderiv ℝ (f p) x) := by
      ext y
      simp
    rw [hid]
    calc
      ‖(A p).symm.toContinuousLinearMap.comp
          ((A p : X →L[ℝ] X) - fderiv ℝ (f p) x)‖
          ≤ ‖(A p).symm.toContinuousLinearMap‖ *
            ‖(A p : X →L[ℝ] X) - fderiv ℝ (f p) x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ L * (K * r) := by
        apply mul_le_mul (hAinv p hp) ?_ (norm_nonneg _) hL.le
        rw [hA p hp, norm_sub_rev]
        exact hbound.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hK)
      _ ≤ 1 / 4 := by nlinarith [hsmall]
  have hresNorm (p : P) (hp : p ∈ U) : ‖(A p).symm (f p 0)‖ ≤ L * ε := by
    calc
      ‖(A p).symm (f p 0)‖ ≤ ‖(A p).symm.toContinuousLinearMap‖ * ‖f p 0‖ :=
        (A p).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ L * ε := mul_le_mul (hAinv p hp) (hres p hp) (norm_nonneg _) hL.le
  obtain ⟨c, hc, hzero, heq⟩ := smooth_small_residual_newton_family U hU f A r hr hf hD
    (fun p hp ↦ (hresNorm p hp).trans hresSmall)
  refine ⟨c, hc, ?_, heq⟩
  intro p hp
  have h := hzero p hp
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
  calc
    ‖c p‖ ≤ (4 / 3 : ℝ) * ‖(A p).symm (f p 0)‖ := h.2.1
    _ ≤ (4 / 3 : ℝ) * (L * ε) := mul_le_mul_of_nonneg_left (hresNorm p hp) (by norm_num)
    _ = (4 / 3 : ℝ) * L * ε := by ring

#print axioms smooth_hessian_small_residual_correction

end GlobalEmbedding.Paper
