import GlobalEmbedding.Paper.CollarAnalyticCoefficientSlices
import GlobalEmbedding.Paper.CollarPeriodicOpenExtension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact

/-!
# Actual little Hölder coefficient power series on an invariant open complex strip

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This is the source-domain application: periodicity and analyticity are
required only inside the invariant open neighborhood containing the actual real orbit slice.
-/

open Set WithLp
open scoped ContDiff NNReal ENNReal Topology

namespace GlobalEmbedding.Paper

/-- A jointly analytic coefficient on an integer-translation-invariant open complex neighborhood
of the real torus slice has an actual complex little Hölder power series in its parameters.

Source: Proposition `prop:collar`, proof lines 530–534, Taylor convergence with three spatial
derivatives. Extend the coefficient by zero outside its invariant open domain. This produces
a total periodic function and preserves all analytic germs on the real slice. The actual
analytic-slice theorem constructs its complex little-space parameter power series, using all
required uniform mixed spatial jet bounds. The image of the fundamental cube is compact and
lies in the open domain, so a positive thickening lies there as well. Small parameter shifts
of that cube lie in the thickening; integer-domain invariance extends this inclusion to the
entire real spatial lift. Shrink the actual series radius to this positive parameter radius.
The extension then agrees with the original coefficient at every required slice point, giving
exactly the source function, not merely an analytic replacement or assumed Banach-valued map.
-/
theorem collar_coefficient_holder_power_series {b a N k : ℕ} {α : ℝ}
    (g : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →
      EuclideanSpace ℂ (Fin N))
    (U : Set (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)))
    (hU : IsOpen U) (z₀ : EuclideanSpace ℂ (Fin b))
    (hslice : ∀ x : EuclideanSpace ℝ (Fin a),
      (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) ∈ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hinv : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ), w + (0, toLp 2 (fun i ↦ (t i : ℂ))) ∈ U ↔ w ∈ U)
    (hperiodic : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)),
      w ∈ U → ∀ (t : Fin a → ℤ), g (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) = g w)
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
  classical
  obtain ⟨G, heq, hper, hAna⟩ := collar_periodic_open_extension g U hU
    (fun t : Fin a → ℤ ↦ (0, toLp 2 (fun i ↦ (t i : ℂ)))) hinv hperiodic
  obtain ⟨r₀, hr₀, F, p, hFp, hsm, hpc, hbound, hF⟩ := collar_analytic_coefficient_slices (k := k) (α := α) G z₀
    (fun x ↦ hAna _ (hslice x) (hg _ (hslice x))) hper hα D hdiam
  let φ (v : Fin a → ℝ) := (z₀, toLp 2 (fun i : Fin a ↦ (v i : ℂ)))
  let K := φ '' Icc (0 : Fin a → ℝ) 1
  have hφ : Continuous φ := continuous_const.prodMk
    ((PiLp.continuous_toLp _ _).comp
      (continuous_pi (fun i ↦ Complex.continuous_ofReal.comp (continuous_apply i))))
  have hK : IsCompact K := isCompact_Icc.image hφ
  have hKU : K ⊆ U := by
    rintro w ⟨v, _, rfl⟩
    exact hslice (toLp 2 v)
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  let σ : ℝ≥0 := NNReal.mk ε hε.le
  have hσ : 0 < σ := by exact_mod_cast hε
  have hsmall (z : EuclideanSpace ℂ (Fin b))
      (hz : z ∈ Metric.eball (0 : EuclideanSpace ℂ (Fin b)) (σ : ℝ≥0∞))
      (x : EuclideanSpace ℝ (Fin a)) :
      (z₀ + z, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) ∈ U := by
    let y : EuclideanSpace ℝ (Fin a) := toLp 2 (fun i ↦ Int.fract (x i))
    let t : Fin a → ℤ := fun i ↦ ⌊x i⌋
    have hy : ofLp y ∈ Icc (0 : Fin a → ℝ) 1 :=
      ⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩
    have hxy : y + toLp 2 (fun i ↦ (t i : ℝ)) = x := by
      ext i
      simp [y, t, Int.fract_add_floor]
    have hmem : (z₀, toLp 2 (fun i : Fin a ↦ (y i : ℂ))) ∈ K := ⟨ofLp y, hy, rfl⟩
    have hznorm : ‖z‖ < ε := by
      have hzdist : dist z 0 < (σ : ℝ) := (edist_lt_coe).mp hz
      simpa only [dist_zero_right, σ, NNReal.coe_mk] using hzdist
    have hdist : dist (z₀ + z, toLp 2 (fun i : Fin a ↦ (y i : ℂ)))
        (z₀, toLp 2 (fun i : Fin a ↦ (y i : ℂ))) < ε := by
      simpa [Prod.dist_eq, dist_eq_norm] using hznorm
    have hUy := hεU (Metric.mem_thickening_iff.mpr ⟨_, hmem, hdist⟩)
    have hpoint : (z₀ + z, toLp 2 (fun i : Fin a ↦ (y i : ℂ))) +
        (0, toLp 2 (fun i ↦ (t i : ℂ))) =
        (z₀ + z, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) := by
      rw [← hxy]
      ext i <;> simp
    rw [← hpoint]
    exact (hinv _ t).mpr hUy
  let ρ : ℝ≥0 := min r₀ σ
  have hρ : 0 < ρ := lt_min hr₀ hσ
  have hρr : (ρ : ℝ≥0∞) ≤ (r₀ : ℝ≥0∞) := by exact_mod_cast (min_le_left r₀ σ)
  have hρσ : (ρ : ℝ≥0∞) ≤ (σ : ℝ≥0∞) := by exact_mod_cast (min_le_right r₀ σ)
  refine ⟨ρ, hρ, F, p, hFp.mono (by exact_mod_cast hρ) hρr, hsm, hpc, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hbound
    refine ⟨M, fun n ↦ ?_⟩
    have hle : (ρ : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast (min_le_left r₀ σ)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ρ.coe_nonneg hle n)
      (norm_nonneg (p n))).trans (hM n)
  · intro z hz y
    exact (hF z ((Metric.eball_subset_eball hρr) hz) y).trans
      (heq _ (hsmall z ((Metric.eball_subset_eball hρσ) hz) y))

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_coefficient_holder_power_series
