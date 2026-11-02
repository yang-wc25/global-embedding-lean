import GlobalEmbedding.Paper.PlanarNativeCurvature
import GlobalEmbedding.Paper.MatrixPeriodicAverageInvariance

/-!
# Actual signed area vanishes under the paper reflection

Source: `main.tex`, `lem:planar`, lines 258–262.
The integrand uses the original map and its actual common orbit derivative.
-/

open Set

namespace GlobalEmbedding.Paper

/-- Actual half-period reflection forces the original signed-area integral to vanish. -/
theorem planar_reflection_signed_area_zero {Q : Type*}
    (R : ℝ → Q → Q) (hzero : ∀ z, R 0 z = z)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (f : Q → Planar) (hf : ∀ z, Differentiable ℝ (fun t : ℝ ↦ f (R t z)))
    (ha : ∀ z, f (R (1 / 2 : ℝ) z) = planarReflection (f z)) (z : Q) :
    orbitAverage R (fun y ↦ f y 0 * orbitDeriv R f y 1 -
      f y 1 * orbitDeriv R f y 0) z = 0 := by
  have hd (y : Q) (i : Fin 2) :
      HasDerivAt (fun t : ℝ ↦ f (R t y) i) (orbitDeriv R f y i) 0 := by
    simpa only [hzero] using planarOrbitCoordinate_hasDerivAt R hadd f hf y 0 i
  have he0 (y : Q) : (fun t : ℝ ↦ f (R t (R (1 / 2 : ℝ) y)) 0) =
      (fun t : ℝ ↦ f (R t y) 0) := by
    funext t
    rw [← hadd, add_comm t (1 / 2), hadd, ha, planarReflection_apply_zero]
  have he1 (y : Q) : (fun t : ℝ ↦ f (R t (R (1 / 2 : ℝ) y)) 1) =
      (fun t : ℝ ↦ -f (R t y) 1) := by
    funext t
    rw [← hadd, add_comm t (1 / 2), hadd, ha, planarReflection_apply_one]
  have hd0 (y : Q) : orbitDeriv R f (R (1 / 2 : ℝ) y) 0 = orbitDeriv R f y 0 := by
    have hh := hd (R (1 / 2 : ℝ) y) 0
    rw [he0] at hh
    exact hh.unique (hd y 0)
  have hd1 (y : Q) : orbitDeriv R f (R (1 / 2 : ℝ) y) 1 = -orbitDeriv R f y 1 := by
    have hh := hd (R (1 / 2 : ℝ) y) 1
    rw [he1] at hh
    exact hh.unique (hd y 1).neg
  let w : Q → ℝ := fun y ↦ f y 0 * orbitDeriv R f y 1 -
    f y 1 * orbitDeriv R f y 0
  have hodd (y : Q) : w (R (1 / 2 : ℝ) y) = -w y := by
    dsimp only [w]
    rw [ha, hd0, hd1, planarReflection_apply_zero, planarReflection_apply_one]
    ring
  have hi : orbitAverage R w (R (1 / 2 : ℝ) z) = orbitAverage R w z := by
    simpa only [orbitAverage,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      MeasureTheory.integral_Icc_eq_integral_Ioc] using
      periodic_average_invariant R hadd hone w z (1 / 2)
  have hn : orbitAverage R w (R (1 / 2 : ℝ) z) = -orbitAverage R w z := by
    unfold orbitAverage
    calc
      _ = ∫ t in (0 : ℝ)..1, -w (R t z) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [← hadd, add_comm t (1 / 2), hadd, hodd]
      _ = _ := intervalIntegral.integral_neg
  change orbitAverage R w z = 0
  linarith

#print axioms planar_reflection_signed_area_zero

end GlobalEmbedding.Paper
