import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
Actual locally uniform lattice-jet bounds for Schwartz functions, used to periodize
an entire-space shifted resolvent. Source: Mathlib lattice p-series and Schwartz
seminorm bounds; W2 original balanced-inverse construction. No PDE solvability is assumed.
-/

open Filter
open scoped SchwartzMap

namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every actual finite-order Schwartz jet has a summable lattice majorant, uniformly on
each norm ball. This includes the zero lattice and the zero-dimensional source. Choose
an exponent above the lattice rank, use the Schwartz weighted seminorm, and compare
`1+‖z‖ ≤ (1+R)(1+‖x+z‖)` on the ball. The reciprocal shifted norm is summable by the
actual Mathlib lattice p-series, with only the single zero lattice point excluded in
the comparison proof. -/
theorem schwartz_lattice_jet_majorant
    (L : Submodule ℤ E) [DiscreteTopology L] (f : 𝓢(E, F))
    (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ v : L → ℝ, Summable v ∧ ∀ (z : L) (x : E), ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k f (x + z)‖ ≤ v z := by
  classical
  let m := Module.finrank ℤ L + 1
  let C : ℝ := 2 ^ m *
    (Finset.Iic (m, k)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w : L → ℝ := fun z => (1 + ‖z‖)⁻¹ ^ m
  have hw : Summable w := by
    apply Summable.of_norm_bounded_eventually
      (ZLattice.summable_norm_pow_inv L m (by dsimp [m]; omega))
    filter_upwards [eventually_cofinite_ne (0 : L)] with z hz
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    dsimp [w]
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity)
      (inv_anti₀ hn (by linarith : ‖z‖ ≤ 1 + ‖z‖)) m
  refine ⟨fun z => (C * (1 + R)^m) * w z, hw.mul_left _, ?_⟩
  intro z x hx
  have ht : 1 + ‖(z : E)‖ ≤ (1 + R) * (1 + ‖x + z‖) := by
    have hn := norm_sub_le (x + (z : E)) x
    rw [add_sub_cancel_left] at hn
    nlinarith [norm_nonneg (x + (z : E))]
  have hs : (1 + ‖x + (z : E)‖)^m * ‖iteratedFDeriv ℝ k f (x + z)‖ ≤ C :=
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (m, k)) le_rfl le_rfl f _
  have hh : (1 + ‖(z : E)‖)^m * ‖iteratedFDeriv ℝ k f (x + z)‖ ≤
      C * (1 + R)^m := calc
    _ ≤ ((1 + R) * (1 + ‖x + (z : E)‖))^m *
        ‖iteratedFDeriv ℝ k f (x + z)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht m) (norm_nonneg _)
    _ = (1 + R)^m * ((1 + ‖x + (z : E)‖)^m *
        ‖iteratedFDeriv ℝ k f (x + z)‖) := by rw [mul_pow]; ring
    _ ≤ (1 + R)^m * C := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := mul_comm _ _
  have hd : ‖iteratedFDeriv ℝ k f (x + z)‖ ≤
      (C * (1 + R)^m) / (1 + ‖(z : E)‖)^m :=
    (le_div_iff₀ (pow_pos (show 0 < 1 + ‖(z : E)‖ by positivity) m)).2
      (by simpa only [mul_comm] using hh)
  simpa only [w, div_eq_mul_inv, inv_pow, Submodule.norm_coe] using hd

#print axioms schwartz_lattice_jet_majorant

end GlobalEmbedding.Paper
