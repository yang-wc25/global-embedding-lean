import GlobalEmbedding.Paper.CollarComplexLinearOfReal
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Abel

/-!
# Bounded mixed complex-bilinear extension for different real input spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The fixed bounded real bilinear correction operator must have an actual
bounded complex-bilinear extension before the analytic fixed-point theorem can be applied.
-/

namespace GlobalEmbedding.Paper

/-- A bounded real bilinear map on two different real forms has a unique bounded complex-bilinear
extension,
with the explicit real/imaginary-coordinate formula. The input real forms may be different,
as for matrix coefficients and vector functions.

Source: Proposition `prop:collar`, proof lines 530–534, complexification of the fixed bilinear Q.
Use the coordinate formula `Q(r x,r y)-Q(s x,s y)+I•(Q(r x,s y)+Q(s x,r y))`.
Each term is bounded real bilinear between the two distinct input spaces. The coordinate
identities under I show that this formula
commutes with multiplication by I in each variable. Upgrade the real continuous linear maps in
the second variable to complex ones. Their unchanged norms bound the resulting outer complex
linear map, making it continuous. This constructs the actual bounded complex bilinear operator.
The real-coordinate identities give agreement with Q on embedded real vectors. Finally expand
any other complex bilinear extension using the decomposition of x and y into real/imaginary
coordinates; its complex bilinearity forces the same formula, hence the extension is unique.
No equality of the real and complex bilinear operator norms is asserted.
-/
theorem collar_complex_mixed_bilinear_extension
    {E U D V F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℂ D]
    [IsScalarTower ℝ ℂ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (ι : U →L[ℝ] E) (r s : E →L[ℝ] U)
    (hdecomp : ∀ x : E, ι (r x) + Complex.I • ι (s x) = x)
    (hrI : ∀ x : E, r (Complex.I • x) = -s x)
    (hsI : ∀ x : E, s (Complex.I • x) = r x)
    (hrι : ∀ u : U, r (ι u) = u) (hsι : ∀ u : U, s (ι u) = 0)
    (κ : V →L[ℝ] D) (r' s' : D →L[ℝ] V)
    (hdecomp' : ∀ y : D, κ (r' y) + Complex.I • κ (s' y) = y)
    (hrI' : ∀ y : D, r' (Complex.I • y) = -s' y)
    (hsI' : ∀ y : D, s' (Complex.I • y) = r' y)
    (hrκ : ∀ v : V, r' (κ v) = v) (hsκ : ∀ v : V, s' (κ v) = 0)
    (Q : U →L[ℝ] V →L[ℝ] F) :
    ∃ C : E →L[ℂ] D →L[ℂ] F,
      (∀ (x : E) (y : D), C x y = Q (r x) (r' y) - Q (s x) (s' y) +
        Complex.I • (Q (r x) (s' y) + Q (s x) (r' y))) ∧
      (∀ (u : U) (v : V), C (ι u) (κ v) = Q u v) ∧
      (∀ B : E →L[ℂ] D →L[ℂ] F,
        (∀ (u : U) (v : V), B (ι u) (κ v) = Q u v) → B = C) := by
  classical
  let piece (a : E →L[ℝ] U) (b : D →L[ℝ] V) : E →L[ℝ] D →L[ℝ] F :=
    ((Q.precompR D).flip b).comp a
  let H : E →L[ℝ] D →L[ℝ] F :=
    piece r r' - piece s s' + Complex.I • (piece r s' + piece s r')
  have hH (x : E) (y : D) : H x y = Q (r x) (r' y) - Q (s x) (s' y) +
      Complex.I • (Q (r x) (s' y) + Q (s x) (r' y)) := rfl
  have hIright (x : E) (y : D) : H x (Complex.I • y) = Complex.I • H x y := by
    simp only [hH, hrI', hsI', map_neg, smul_add, smul_sub, smul_neg,
      smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  have hIleft (x : E) (y : D) : H (Complex.I • x) y = Complex.I • H x y := by
    simp only [hH, hrI, hsI, map_neg, neg_apply, smul_add, smul_sub,
      smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  have hscalarleft (c : ℂ) (x : E) (y : D) : H (c • x) y = c • H x y := by
    obtain ⟨C, hC, hnorm⟩ := collar_complex_linear_of_real (H.flip y) (fun x ↦ hIleft x y)
    have heval (z : E) : C z = H z y :=
      congrArg (fun L : E →L[ℝ] F ↦ L z) hC
    rw [← heval (c • x), ← heval x]
    exact C.map_smul c x
  have hright (x : E) : ∃ C : D →L[ℂ] F,
      C.restrictScalars ℝ = H x ∧ ‖C‖ = ‖H x‖ :=
    collar_complex_linear_of_real (H x) (hIright x)
  let Uc : E → D →L[ℂ] F := fun x ↦ Classical.choose (hright x)
  have hUc (x : E) : (Uc x).restrictScalars ℝ = H x :=
    (Classical.choose_spec (hright x)).1
  have hUcnorm (x : E) : ‖Uc x‖ = ‖H x‖ :=
    (Classical.choose_spec (hright x)).2
  have hUceval (x : E) (y : D) : Uc x y = H x y :=
    congrArg (fun L : D →L[ℝ] F ↦ L y) (hUc x)
  let L : E →ₗ[ℂ] D →L[ℂ] F :=
    { toFun := Uc
      map_add' := by
        intro x y
        ext z
        change Uc (x + y) z = Uc x z + Uc y z
        simp only [hUceval]
        exact congrArg (fun K : D →L[ℝ] F ↦ K z) (H.map_add x y)
      map_smul' := by
        intro c x
        ext y
        change Uc (c • x) y = c • Uc x y
        simp only [hUceval]
        exact hscalarleft c x y }
  let C : E →L[ℂ] D →L[ℂ] F := L.mkContinuous ‖H‖ (fun x ↦ by
    change ‖Uc x‖ ≤ ‖H‖ * ‖x‖
    rw [hUcnorm]
    exact H.le_opNorm x)
  have hC (x : E) (y : D) : C x y = Q (r x) (r' y) - Q (s x) (s' y) +
      Complex.I • (Q (r x) (s' y) + Q (s x) (r' y)) := by
    change Uc x y = _
    rw [hUceval, hH]
  refine ⟨C, hC, ?_, ?_⟩
  · intro u v
    simp only [hC, hrι, hsι, hrκ, hsκ, map_zero, zero_apply, sub_zero,
      smul_zero, add_zero]
  · intro B hD
    have hformula (x : E) (y : D) : B x y = Q (r x) (r' y) - Q (s x) (s' y) +
        Complex.I • (Q (r x) (s' y) + Q (s x) (r' y)) := by
      conv_lhs => rw [← hdecomp x, ← hdecomp' y]
      simp only [map_add, map_smul, add_apply,
        smul_apply, hD, smul_add, smul_smul, Complex.I_mul_I,
        neg_one_smul]
      abel
    ext x y
    rw [hformula, hC]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_mixed_bilinear_extension
