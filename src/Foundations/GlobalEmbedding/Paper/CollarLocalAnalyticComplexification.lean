import GlobalEmbedding.Paper.CollarRealMultilinearComplexification
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Actual local complex extension of a finite-dimensional real analytic map

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Construct the local extension before any compact periodic gluing.
-/

open Set
open scoped NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- A real analytic map on finite real coordinate space with complex Banach target has an
actual complex analytic extension on a positive complex ball, agreeing on all real points
in that ball.

Source: Proposition `prop:collar`, proof lines 530–534, finite-dimensional coefficient
complexification. Take a genuine real norm power series. Complexify every actual multilinear
coefficient by its finite-coordinate formula. The proved m^n coefficient norm bound preserves
a positive convergence radius after shrinking by max(1,m). Sum the actual complex series at
the complexified base point. On all nearby real points its diagonal terms equal the original
real Taylor terms, so uniqueness of a convergent sum proves exact agreement. This is a
local construction; periodic gluing and the common torus strip are separate obligations. -/
theorem collar_local_analytic_complexification
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    {m : ℕ} (f : (Fin m → ℝ) → F) (x : Fin m → ℝ) (hf : AnalyticAt ℝ f x) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∃ g : (Fin m → ℂ) → F,
      AnalyticOnNhd ℂ g (Metric.eball (fun j ↦ (x j : ℂ)) (ρ : ℝ≥0∞)) ∧
      (∀ y : Fin m → ℝ, ‖y - x‖ < (ρ : ℝ) → g (fun j ↦ (y j : ℂ)) = f y) := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨R, hR, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hRpos : 0 < R := by exact_mod_cast hR
  let c : ℝ≥0 := max 1 (m : ℝ≥0)
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := zero_lt_one.trans_le hc1
  let ρ : ℝ≥0 := R / c
  have hρ : 0 < ρ := div_pos hRpos hcpos
  have hρR : ρ ≤ R := div_le_self zero_le hc1
  have hcρ : (c : ℝ) * (ρ : ℝ) = R := by
    change (c : ℝ) * ((R : ℝ) / (c : ℝ)) = R
    field_simp
  let q : FormalMultilinearSeries ℂ (Fin m → ℂ) F :=
    fun n ↦ collarRealMultilinearComplexification (p n)
  obtain ⟨M, _, hM⟩ := p.norm_mul_pow_le_of_lt_radius (hRr.trans_le hp.r_le)
  have hqbound (n : ℕ) : ‖q n‖ * (ρ : ℝ) ^ n ≤ M := by
    calc
      _ ≤ ((m : ℝ) ^ n * ‖p n‖) * (ρ : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (collar_real_multilinear_complexification_norm (p n))
          (pow_nonneg ρ.coe_nonneg n)
      _ ≤ ((c : ℝ) ^ n * ‖p n‖) * (ρ : ℝ) ^ n := by
        gcongr
        change (m : ℝ) ≤ max 1 (m : ℝ)
        exact le_max_right _ _
      _ = ‖p n‖ * ((c : ℝ) * (ρ : ℝ)) ^ n := by rw [mul_pow]; ring
      _ ≤ M := by rw [hcρ]; exact hM n
  have hqr : (ρ : ℝ≥0∞) ≤ q.radius := q.le_radius_of_bound M hqbound
  let xc : Fin m → ℂ := fun j ↦ (x j : ℂ)
  let g : (Fin m → ℂ) → F := fun z ↦ q.sum (z - xc)
  have hgp : HasFPowerSeriesOnBall g q xc (ρ : ℝ≥0∞) := by
    refine ⟨hqr, by exact_mod_cast hρ, ?_⟩
    intro z hz
    simpa only [g, add_sub_cancel_left] using q.hasSum (Metric.eball_subset_eball hqr hz)
  refine ⟨ρ, hρ, g, hgp.analyticOnNhd, ?_⟩
  intro y hy
  have hrealnorm (v : Fin m → ℝ) : ‖(fun j ↦ (v j : ℂ))‖ = ‖v‖ := by
    have hi := Isometry.piMap (fun _ : Fin m ↦ ((↑) : ℝ → ℂ))
      (fun _ ↦ Complex.isometry_ofReal)
    have hz : Pi.map (fun _ : Fin m ↦ ((↑) : ℝ → ℂ)) 0 = 0 := by
      ext j
      rfl
    have he := hi.dist_eq v 0
    rw [hz, dist_zero_right, dist_zero_right] at he
    exact he
  have hyd : y - x ∈ Metric.eball (0 : Fin m → ℝ) r := by
    apply (Metric.eball_subset_eball hRr.le)
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact (ENNReal.ofReal_lt_coe_iff (norm_nonneg _)).mpr
      (hy.trans_le (by exact_mod_cast hρR))
  have hyc : (fun j ↦ ((y - x) j : ℂ)) ∈ Metric.eball (0 : Fin m → ℂ) (ρ : ℝ≥0∞) := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, hrealnorm]
    exact (ENNReal.ofReal_lt_coe_iff (norm_nonneg _)).mpr hy
  have hsum := hgp.hasSum hyc
  have hpsum := hp.hasSum hyd
  have heq : (fun n ↦ q n (fun _ : Fin n ↦ fun j ↦ ((y - x) j : ℂ))) =
      fun n ↦ p n (fun _ : Fin n ↦ y - x) := by
    funext n
    exact collar_real_multilinear_complexification_real (p n) (fun _ ↦ y - x)
  rw [heq] at hsum
  have hcenter : xc + (fun j ↦ ((y - x) j : ℂ)) = fun j ↦ (y j : ℂ) := by
    ext j
    simp [xc]
  simpa only [hcenter, add_sub_cancel] using hsum.unique hpsum

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_local_analytic_complexification
