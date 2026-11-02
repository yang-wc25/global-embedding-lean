import Round2.GaugeOrbit
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Exact removal of the spatial normal-coordinate derivative at incidence zeros

Write the actual normal coordinate operator as `T`, the actual first jet as
`L`, and the actual normalized Hessian as `H`.  The identity `T L = 0` yields
`(DT)L = -T(DL)`.  At one point use the geometric splitting
`R T + L K = id`.  Then `DT H` is the sum of a target-coordinate orbit term
and `-T(DL)K H`.  Any native incidence derivative which kills the former has
an estimate involving only `T`, the first three map jets and `K`; no norm of
`DT` appears.  The tangent component of the Hessian is retained explicitly.
-/

noncomputable section
open Filter
open scoped Topology

namespace GlobalEmbedding.Upgrade

variable {X E S V W Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Native differentiation of the fact that the actual normal coordinate
operator kills the actual tangent image. -/
theorem fderiv_normal_tangent_constraint
    (T : X → V →L[ℝ] W) (L : X → E →L[ℝ] V) (x : X)
    (hT : DifferentiableAt ℝ T x) (hL : DifferentiableAt ℝ L x)
    (hTL : ∀ᶠ z in 𝓝 x, (T z).comp (L z) = 0) (d : X) :
    (fderiv ℝ T x d).comp (L x) = -(T x).comp (fderiv ℝ L x d) := by
  have hz : fderiv ℝ (fun z ↦ (T z).comp (L z)) x = 0 := by
    have he : (fun z ↦ (T z).comp (L z)) =ᶠ[𝓝 x] (fun _ ↦ 0) := hTL
    rw [he.fderiv_eq]
    exact fderiv_const_apply _
  have h := DFunLike.congr_fun hz d
  rw [fderiv_clm_comp hT hL] at h
  change (T x).comp (fderiv ℝ L x d) + (fderiv ℝ T x d).comp (L x) = 0 at h
  exact eq_neg_of_add_eq_zero_right h

/-- Exact product-rule cancellation in the actual incidence differential.
`R` is used only algebraically: no derivative or bound for it is required. -/
theorem fderiv_incidence_gauge_cancellation
    (T : X → V →L[ℝ] W) (L : X → E →L[ℝ] V)
    (H : X → S →L[ℝ] V) (x : X)
    (hT : DifferentiableAt ℝ T x) (hL : DifferentiableAt ℝ L x)
    (hH : DifferentiableAt ℝ H x)
    (hTL : ∀ᶠ z in 𝓝 x, (T z).comp (L z) = 0)
    (R : W →L[ℝ] V) (K : V →L[ℝ] E)
    (hsplit : R.comp (T x) + (L x).comp K = ContinuousLinearMap.id ℝ V)
    (D : (S →L[ℝ] W) →L[ℝ] Y)
    (hD : ∀ A : W →L[ℝ] W, D (A.comp ((T x).comp (H x))) = 0)
    (d : X) :
    D (fderiv ℝ (fun z ↦ (T z).comp (H z)) x d) =
      D ((T x).comp (fderiv ℝ H x d) -
        (T x).comp ((fderiv ℝ L x d).comp (K.comp (H x)))) := by
  have hc := fderiv_normal_tangent_constraint T L x hT hL hTL d
  have he : (fderiv ℝ T x d).comp (H x) =
      ((fderiv ℝ T x d).comp R).comp ((T x).comp (H x)) -
        (T x).comp ((fderiv ℝ L x d).comp (K.comp (H x))) := by
    calc
      _ = (fderiv ℝ T x d).comp
          ((R.comp (T x) + (L x).comp K).comp (H x)) := by rw [hsplit]; rfl
      _ = ((fderiv ℝ T x d).comp R).comp ((T x).comp (H x)) +
          ((fderiv ℝ T x d).comp (L x)).comp (K.comp (H x)) := by
        ext v
        simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]
      _ = _ := by
        rw [hc]
        ext v
        simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, neg_apply, map_neg, sub_eq_add_neg]
  rw [fderiv_clm_comp hT hH]
  change D ((T x).comp (fderiv ℝ H x d) + (fderiv ℝ T x d).comp (H x)) = _
  rw [he]
  simp only [map_add, map_sub, map_neg, hD, zero_sub, zero_add, sub_eq_add_neg]

/-- Bound for the composed native incidence derivative. This replaces an
unneeded bound for the full coordinate derivative by one valid at zeros. -/
theorem norm_incidence_derivative_without_gauge_bound
    (T : X → V →L[ℝ] W) (L : X → E →L[ℝ] V)
    (H : X → S →L[ℝ] V) (x : X)
    (hT : DifferentiableAt ℝ T x) (hL : DifferentiableAt ℝ L x)
    (hH : DifferentiableAt ℝ H x)
    (hTL : ∀ᶠ z in 𝓝 x, (T z).comp (L z) = 0)
    (R : W →L[ℝ] V) (K : V →L[ℝ] E)
    (hsplit : R.comp (T x) + (L x).comp K = ContinuousLinearMap.id ℝ V)
    (D : (S →L[ℝ] W) →L[ℝ] Y)
    (hD : ∀ A : W →L[ℝ] W, D (A.comp ((T x).comp (H x))) = 0) :
    ‖D.comp (fderiv ℝ (fun z ↦ (T z).comp (H z)) x)‖ ≤
      ‖D‖ * ‖T x‖ * (‖fderiv ℝ H x‖ + ‖fderiv ℝ L x‖ * ‖K‖ * ‖H x‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  rw [ContinuousLinearMap.comp_apply,
    fderiv_incidence_gauge_cancellation T L H x hT hL hH hTL R K hsplit D hD d]
  calc
    _ ≤ ‖D‖ * ‖(T x).comp (fderiv ℝ H x d) -
        (T x).comp ((fderiv ℝ L x d).comp (K.comp (H x)))‖ := D.le_opNorm _
    _ ≤ ‖D‖ * (‖(T x).comp (fderiv ℝ H x d)‖ +
        ‖(T x).comp ((fderiv ℝ L x d).comp (K.comp (H x)))‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ ‖D‖ * (‖T x‖ * ‖fderiv ℝ H x d‖ +
        ‖T x‖ * (‖fderiv ℝ L x d‖ * (‖K‖ * ‖H x‖))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (by positivity))) (by positivity))
    _ ≤ ‖D‖ * (‖T x‖ * (‖fderiv ℝ H x‖ * ‖d‖) +
        ‖T x‖ * ((‖fderiv ℝ L x‖ * ‖d‖) * (‖K‖ * ‖H x‖))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_left ((fderiv ℝ H x).le_opNorm d) (by positivity))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ((fderiv ℝ L x).le_opNorm d) (by positivity))
          (by positivity))
    _ = _ := by ring

#print axioms fderiv_normal_tangent_constraint
#print axioms fderiv_incidence_gauge_cancellation
#print axioms norm_incidence_derivative_without_gauge_bound

end GlobalEmbedding.Upgrade
