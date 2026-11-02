import Initialization.Geometry.NormalizedCutoffJets
import Initialization.Geometry.BoundedScaledAtlas

/-!
# Actual cutoff budgets on the fixed rescaled coordinate balls

All cutoff derivative bounds used by the literal waves are now produced from
the actual compact source. This file consumes the actual geometry producer;
there is no derivative, overlap, normalization, or transition assumption.
-/

noncomputable section
open Set Function Metric Manifold IsManifold
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

/-- The original small parameter is uniformly bounded and dominates K/T for
all original real parameters. No integer-frequency restriction is introduced. -/
theorem initialization_error_scale_bounds {K T : ℝ} (hK : 1 ≤ K) (hKT : K ≤ T) :
    0 ≤ K / T ∧ K / T ≤ 1 ∧ 0 ≤ K⁻¹ + K / T ∧
      K / T ≤ K⁻¹ + K / T ∧ K⁻¹ + K / T ≤ 2 := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hTpos : 0 < T := hKpos.trans_le hKT
  have hq : 0 ≤ K / T := div_nonneg hKpos.le hTpos.le
  have hq1 : K / T ≤ 1 := (div_le_one hTpos).mpr hKT
  have hi : 0 ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
  have hi1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  exact ⟨hq, hq1, by positivity, by linarith, by linarith⟩

/-- The actual cutoff pullback is smooth on the whole fixed coordinate ball. -/
theorem actualCutoffPullback_contDiffOn {G : PreparedCharts M n} {K T : ℝ}
    (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (p : Fin Q.count) (i : Fin F.count) :
    ContDiffOn ℝ ∞ (F.cutoff i ∘ ((Q.boundedAtlas hT).chart p).symm)
      (ball 0 G.scaleRadius) :=
  ((F.cutoff_smooth i).comp_contMDiffOn
    (contMDiffOn_symm_of_mem_maximalAtlas ((Q.boundedAtlas_smooth hT).chart_mem p))).contDiffOn

/-- A single prepared budget supplies all derivatives through j and gives
every positive cutoff derivative the original small factor K⁻¹+K/T. The sequence
is selected before both scales and all scale-dependent net choices. -/
theorem exists_actual_cutoff_wave_budgets (G : PreparedCharts M n) :
    ∃ A : ℕ → ℝ, (∀ j, 1 ≤ A j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
        (p : Fin Q.count) (i : Fin F.count) (j : ℕ)
        (y : EuclideanSpace ℝ (Fin n)), y ∈ ball 0 G.scaleRadius →
        (∀ k ≤ j, ‖iteratedFDeriv ℝ k
          (F.cutoff i ∘ ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y‖ ≤ A j) ∧
        (∀ k ≤ j, ‖iteratedFDeriv ℝ (k+1)
          (F.cutoff i ∘ ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y‖ ≤
            A j * (K⁻¹ + K / T)) := by
  obtain ⟨B, hB, hb⟩ := exists_rescaled_normalizedCutoff_derivative_bounds G
  let A : ℕ → ℝ := fun j ↦ 1 + ∑ k ∈ Finset.range (j+2), B k
  have hA (j : ℕ) : 1 ≤ A j := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (j+2), B k := Finset.sum_nonneg fun k _ ↦ hB k
    dsimp [A]
    linarith
  have hBA {k j : ℕ} (hk : k ≤ j+1) : B k ≤ A j := by
    have hs : B k ≤ ∑ k ∈ Finset.range (j+2), B k :=
      Finset.single_le_sum (fun k _ ↦ hB k) (by simp; omega)
    dsimp [A]
    linarith
  refine ⟨A, hA, ?_⟩
  intro K T hK hKT F Q p i j y hy
  have hcore := Q.scaledPoint_in_open_core (hK.trans hKT) p hy
  obtain ⟨hq0, hq1, hδ0, hqδ, _⟩ := initialization_error_scale_bounds hK hKT
  have hbound (k : ℕ) : ‖iteratedFDeriv ℝ k
      (F.cutoff i ∘ ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y‖ ≤ B k * (K/T)^k :=
    hb K T hK hKT F Q p i k y hcore
  constructor
  · intro k hk
    exact (hbound k).trans ((mul_le_of_le_one_right (hB k) (pow_le_one₀ hq0 hq1)).trans
      (hBA (by omega)))
  · intro k hk
    calc
      _ ≤ B (k+1) * (K/T)^(k+1) := hbound (k+1)
      _ ≤ B (k+1) * (K/T) := mul_le_mul_of_nonneg_left
        (pow_le_of_le_one hq0 hq1 (by omega)) (hB (k+1))
      _ ≤ A j * (K⁻¹ + K/T) := mul_le_mul (hBA (by omega)) hqδ hq0
        (zero_le_one.trans (hA j))

end GlobalEmbedding.Initialization
