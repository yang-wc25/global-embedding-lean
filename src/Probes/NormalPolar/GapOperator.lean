import NormalPolar.InverseSqrtSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Zeroth-order alignment of the explicit polar operator

The series and the polar expression are exactly the definitions used by the
construction and response files. A derivative bound obtained from the actual
analytic series on a fixed compact operator ball yields a uniform modulus.
The conclusion does not assume proximity of the polar operator itself.
-/

noncomputable section
open Set
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Algebraic comparison for the precise new-to-old polar expression. -/
theorem norm_polar_expression_sub_projection_le
    (S P R : V →L[ℝ] V) (hP : P * P = P)
    (hPn : ‖P‖ ≤ 1) (hRn : ‖R‖ ≤ 1) :
    ‖S * P * R - P‖ ≤ ‖S - 1‖ + ‖R - P‖ := by
  have hid : S * P * R - P = (S - 1) * P * R + P * (R - P) := by
    simp only [sub_mul, mul_sub, one_mul, hP]
    abel
  have hPR : ‖(S - 1) * P * R‖ ≤ ‖S - 1‖ := by
    calc
      _ ≤ (‖S - 1‖ * ‖P‖) * ‖R‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖S - 1‖ * 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hPn (norm_nonneg _)) hRn
          (norm_nonneg _) (by positivity)
      _ = ‖S - 1‖ := by ring
  have hRP : ‖P * (R - P)‖ ≤ ‖R - P‖ := by
    exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right hPn (norm_nonneg _)).trans_eq (one_mul _))
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hPR hRP)

variable [CompleteSpace V] [FiniteDimensional ℝ V]

/-- The actual analytic inverse-square-root series has a uniform first-order
modulus on one fixed ball. The constant is constructed by compactness. -/
theorem exists_actualInvSqrt_sub_one_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : V →L[ℝ] V, ‖E‖ ≤ (1 / 2 : ℝ) →
      ‖actualInvSqrt E - 1‖ ≤ C * ‖E‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_actualInvSqrt_derivative_bound (V := V)
  refine ⟨C, hC, fun E hE ↦ ?_⟩
  have hd (T : V →L[ℝ] V) (hT : T ∈ Metric.closedBall 0 (1 / 2 : ℝ)) :
      DifferentiableAt ℝ actualInvSqrt T := by
    have ht : ‖T‖ ≤ (1 / 2 : ℝ) := by simpa using hT
    exact (contDiffAt_actualInvSqrt T (ht.trans_lt (by norm_num))).differentiableAt (by simp)
  have hb (T : V →L[ℝ] V) (hT : T ∈ Metric.closedBall 0 (1 / 2 : ℝ)) :
      ‖fderiv ℝ actualInvSqrt T‖ ≤ C := hbound T (by simpa using hT)
  have h := (convex_closedBall (0 : V →L[ℝ] V) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    hd hb (show (0 : V →L[ℝ] V) ∈ Metric.closedBall 0 (1 / 2 : ℝ) by simp)
    (show E ∈ Metric.closedBall 0 (1 / 2 : ℝ) by simpa using hE)
  simpa using h

/-- One constant controls every pair of actual orthogonal projections in the
same finite dimensional ambient space. It is independent of all geometric
parameters, source points, supports and dimensions of the projection ranges. -/
theorem exists_actualPolarOperator_gap_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P R : V →L[ℝ] V,
      P * P = P → ‖P‖ ≤ 1 → ‖R‖ ≤ 1 → ∀ ε : ℝ,
      0 ≤ ε → ε ≤ (1 / 2 : ℝ) → ‖R - P‖ ≤ ε →
        ‖actualPolarOperator P R - P‖ ≤ C * ε ^ 2 + ε := by
  obtain ⟨C, hC, hbound⟩ := exists_actualInvSqrt_sub_one_bound (V := V)
  refine ⟨C, hC, ?_⟩
  intro P R hP hPn hRn ε hε hεsmall hgap
  have hPR : ‖P - R‖ ≤ ε := by simpa only [norm_sub_rev] using hgap
  have hEsq : ‖(P - R) ^ 2‖ ≤ ε ^ 2 := by
    calc
      _ ≤ ‖P - R‖ ^ 2 := by simpa only [pow_two] using norm_mul_le (P - R) (P - R)
      _ ≤ ε ^ 2 := sq_le_sq₀ (norm_nonneg _) hε |>.mpr hPR
  have hE : ‖(P - R) ^ 2‖ ≤ (1 / 2 : ℝ) := by nlinarith
  calc
    _ ≤ ‖actualInvSqrt ((P - R) ^ 2) - 1‖ + ‖R - P‖ :=
      norm_polar_expression_sub_projection_le _ P R hP hPn hRn
    _ ≤ C * ‖(P - R) ^ 2‖ + ε := add_le_add (hbound _ hE) hgap
    _ ≤ C * ε ^ 2 + ε := add_le_add (mul_le_mul_of_nonneg_left hEsq hC) le_rfl

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.norm_polar_expression_sub_projection_le
#print axioms GlobalEmbedding.NormalPolar.exists_actualInvSqrt_sub_one_bound
#print axioms GlobalEmbedding.NormalPolar.exists_actualPolarOperator_gap_bound
