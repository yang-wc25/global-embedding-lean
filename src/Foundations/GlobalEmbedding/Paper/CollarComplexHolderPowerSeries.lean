import GlobalEmbedding.Paper.CollarComplexMultilinearCoefficient
import GlobalEmbedding.Paper.CollarComplexHolderEvaluation
import Mathlib.Analysis.Analytic.Basic

/-!
# Actual complex little Hölder power series from spatial coefficient bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The actual complex Banach model has been constructed with the exact source norm. The
source-specific uniform Taylor bounds remain a separate genuine prerequisite.
-/

open Set WithLp
open scoped ContDiff NNReal ENNReal Topology

namespace GlobalEmbedding.Paper

/-- Smooth periodic complex pointwise Taylor coefficients with uniform spatial-jet bounds and a
positive weighted norm radius construct an actual complex little-Hölder analytic family.

Source: Proposition `prop:collar`, proof lines 530–534, uniform parameter Taylor convergence
with three spatial derivatives. First construct the actual continuous multilinear coefficient
in the actual little space from each smooth periodic pointwise coefficient and its jet bounds.
Their weighted norm bounds give the asserted positive radius. Completeness of the actual
little space yields a norm sum, which defines the family. At every real orbit point, bounded
evaluation transports this norm sum to the pointwise coefficient series. Its prescribed Taylor
sum agrees with the given pointwise family by uniqueness of sums, so the norm-valued family
has exactly the required underlying lift throughout the parameter ball. No complex Holder-valued
family, coefficient continuity, slice membership or completeness assumption is supplied.
-/
theorem collar_complex_holder_power_series
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {a N k : ℕ} {α : ℝ}
    (g : Z → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N))
    (G : (n : ℕ) → MultilinearMap ℂ (fun _ : Fin n ↦ Z)
      (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N)))
    (hsmooth : ∀ n m, ContDiff ℝ ∞ (G n m))
    (hperiodic : ∀ n (m : Fin n → Z) (x : EuclideanSpace ℝ (Fin a))
      (t : Fin a → ℤ), G n m (x + toLp 2 (fun i ↦ (t i : ℝ))) = G n m x)
    (C : ℕ → ℕ → ℝ) (hCnonneg : ∀ n j, j ≤ k + 1 → 0 ≤ C n j)
    (hjet : ∀ n (m : Fin n → Z) j, j ≤ k + 1 →
      ∀ x : EuclideanSpace ℝ (Fin a), (∀ i, x i ∈ Icc (0 : ℝ) 1) →
        ‖iteratedFDeriv ℝ j (G n m) x‖ ≤ C n j * ∏ i : Fin n, ‖m i‖)
    (hα : α ≤ 1) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D)
    (z₀ : Z) (ρ : ℝ≥0) (hρ : 0 < ρ) (M : ℝ)
    (hbound : ∀ n, ((∑ j ∈ Finset.range (k + 1), C n j) +
      C n (k + 1) * D ^ (1 - α)) * (ρ : ℝ) ^ n ≤ M)
    (hpoint : ∀ z ∈ Metric.eball (0 : Z) (ρ : ℝ≥0∞),
      ∀ y : EuclideanSpace ℝ (Fin a),
      HasSum (fun n : ℕ ↦ G n (fun _ : Fin n ↦ z) y) (g (z₀ + z) y)) :
    ∃ (F : Z → CollarComplexHolderSpace a N k α)
      (p : FormalMultilinearSeries ℂ Z (CollarComplexHolderSpace a N k α)),
      HasFPowerSeriesOnBall F p z₀ (ρ : ℝ≥0∞) ∧
      (∀ n m, collarComplexHolderFunction (p n m) = G n m) ∧
      (∀ n, ‖p n‖ ≤ (∑ j ∈ Finset.range (k + 1), C n j) +
        C n (k + 1) * D ^ (1 - α)) ∧
      (∀ z ∈ Metric.eball (0 : Z) (ρ : ℝ≥0∞),
        collarComplexHolderFunction (F (z₀ + z)) = g (z₀ + z)) := by
  classical
  have hcoeff (n : ℕ) := collar_complex_multilinear_coefficient
    (G n) (hsmooth n) (hperiodic n) (C n) (hCnonneg n) (hjet n) α hα D hdiam
  choose p hp hnorm using hcoeff
  have hradius : (ρ : ℝ≥0∞) ≤ FormalMultilinearSeries.radius p := by
    apply FormalMultilinearSeries.le_radius_of_bound _ M
    intro n
    exact (mul_le_mul_of_nonneg_right (hnorm n) (pow_nonneg ρ.coe_nonneg n)).trans
      (hbound n)
  let F : Z → CollarComplexHolderSpace a N k α :=
    fun z ↦ ∑' n : ℕ, p n (fun _ : Fin n ↦ z - z₀)
  have hsum (z : Z) (hz : z ∈ Metric.eball (0 : Z) (ρ : ℝ≥0∞)) :=
    FormalMultilinearSeries.summable p ((Metric.eball_subset_eball hradius) hz)
  have hF (z : Z) : F (z₀ + z) = ∑' n : ℕ, p n (fun _ : Fin n ↦ z) := by
    simp only [F, add_sub_cancel_left]
  refine ⟨F, p, ⟨hradius, by exact_mod_cast hρ, ?_⟩, hp, hnorm, ?_⟩
  · intro z hz
    simpa only [← hF] using (hsum z hz).hasSum
  · intro z hz
    funext y
    obtain ⟨ev, hev, _⟩ := collar_complex_holder_evaluation (k := k) (α := α) y
    have hnormsum := ev.hasSum (hsum z hz).hasSum
    have hpointsum : HasSum (fun n : ℕ ↦ ev (p n (fun _ : Fin n ↦ z)))
        (g (z₀ + z) y) := by
      simpa only [hev, hp] using hpoint z hz y
    rw [← hev, hF]
    exact hnormsum.unique hpointsum

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_holder_power_series
