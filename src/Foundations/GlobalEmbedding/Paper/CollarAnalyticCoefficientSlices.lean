import GlobalEmbedding.Paper.CollarCanonicalMixedJetBounds
import GlobalEmbedding.Paper.CollarComplexHolderPowerSeries

/-!
# Actual analytic little Hölder slices of a jointly analytic periodic coefficient

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Actual joint analyticity and integer periodicity construct the complex
little-Hölder power series, with no assumed Banach-valued holomorphic-to-analytic conversion.
-/

open Set WithLp
open scoped ContDiff NNReal ENNReal Topology

namespace GlobalEmbedding.Paper

/-- A genuinely jointly complex analytic periodic finite-dimensional coefficient constructs
an actual complex little Hölder family with a norm-convergent parameter power series and
exactly the prescribed complex-valued slices near the base parameter.

Source: Proposition `prop:collar`, proof lines 530–534, Taylor convergence with three spatial
derivatives. Extract the actual canonical smooth periodic coefficients, a common positive
parameter radius, actual pointwise Taylor sums and uniform weighted spatial jet bounds through
k+1. Divide those bounds by the positive radius to the coefficient degree to obtain the exact
jet inputs for the actual complex coefficient construction. The finite jet norm expression,
multiplied back by that radius power, has one common bound. The actual complex little-space
series assembly then constructs a family and an actual HasFPowerSeriesOnBall. Its bounded
evaluations identify every prescribed slice on that parameter ball. No coefficient estimates,
Holder-valued family, slice membership, Taylor sums or completeness are supplied as assumptions.
-/
theorem collar_analytic_coefficient_slices {b a N k : ℕ} {α : ℝ}
    (g : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →
      EuclideanSpace ℂ (Fin N))
    (z₀ : EuclideanSpace ℂ (Fin b))
    (hg : ∀ x : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℂ g (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))))
    (hperiodic : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ), g (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) = g w)
    (hα : α ≤ 1) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧
      ∃ (F : EuclideanSpace ℂ (Fin b) → CollarComplexHolderSpace a N k α)
        (p : FormalMultilinearSeries ℂ (EuclideanSpace ℂ (Fin b))
          (CollarComplexHolderSpace a N k α)),
        HasFPowerSeriesOnBall F p z₀ (ρ : ℝ≥0∞) ∧
        (∀ n m, ContDiff ℝ ∞ (collarComplexHolderFunction (p n m))) ∧
        (∀ n m (x : EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ),
          collarComplexHolderFunction (p n m) (x + toLp 2 (fun i ↦ (t i : ℝ))) =
            collarComplexHolderFunction (p n m) x) ∧
        (∃ M : ℝ, ∀ n : ℕ, ‖p n‖ * (ρ : ℝ) ^ n ≤ M) ∧
        (∀ z ∈ Metric.eball (0 : EuclideanSpace ℂ (Fin b)) (ρ : ℝ≥0∞),
          ∀ y : EuclideanSpace ℝ (Fin a),
          collarComplexHolderFunction (F (z₀ + z)) y =
            g (z₀ + z, toLp 2 (fun i : Fin a ↦ (y i : ℂ)))) := by
  obtain ⟨G, hsmooth, hper, ρ, hρ, M, hjets, hpoint⟩ :=
    collar_canonical_mixed_jet_bounds (k := k) g z₀ hg hperiodic
  have hρreal : 0 < (ρ : ℝ) := by exact_mod_cast hρ
  let C (n j : ℕ) : ℝ := (M j : ℝ) / (ρ : ℝ) ^ n
  have hC : ∀ n j, j ≤ k + 1 → 0 ≤ C n j := by
    intro n j _
    exact div_nonneg (M j).coe_nonneg (pow_nonneg ρ.coe_nonneg n)
  have hjet : ∀ n (m : Fin n → EuclideanSpace ℂ (Fin b)) j, j ≤ k + 1 →
      ∀ x : EuclideanSpace ℝ (Fin a), (∀ i, x i ∈ Icc (0 : ℝ) 1) →
        ‖iteratedFDeriv ℝ j (G n m) x‖ ≤ C n j * ∏ i : Fin n, ‖m i‖ := by
    intro n m j hj x hx
    change _ ≤ ((M j : ℝ) / (ρ : ℝ) ^ n) * _
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (pow_pos hρreal n)).mpr (hjets n j hj m x hx)
  let K : ℝ := (∑ j ∈ Finset.range (k + 1), (M j : ℝ)) +
    (M (k + 1) : ℝ) * D ^ (1 - α)
  have hbound (n : ℕ) : ((∑ j ∈ Finset.range (k + 1), C n j) +
      C n (k + 1) * D ^ (1 - α)) * (ρ : ℝ) ^ n ≤ K := by
    apply le_of_eq
    dsimp only [C, K]
    rw [← Finset.sum_div]
    field_simp [ne_of_gt (pow_pos hρreal n)]
  obtain ⟨F, p, hFp, hp, hpnorm, hF⟩ := collar_complex_holder_power_series
    (fun z y ↦ g (z, toLp 2 (fun i : Fin a ↦ (y i : ℂ))))
    G hsmooth hper C hC hjet hα D hdiam z₀ ρ hρ K hbound
    (fun z hz y ↦ hpoint y z hz)
  refine ⟨ρ, hρ, F, p, hFp, ?_, ?_, ?_, ?_⟩
  · intro n m
    rw [hp]
    exact hsmooth n m
  · intro n m x t
    rw [hp]
    exact hper n m x t
  · refine ⟨K, fun n ↦ ?_⟩
    exact (mul_le_mul_of_nonneg_right (hpnorm n) (pow_nonneg ρ.coe_nonneg n)).trans
      (hbound n)
  · intro z hz y
    exact congrFun (hF z hz) y

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_analytic_coefficient_slices
