import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A common complex base neighborhood and imaginary torus strip

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Coordinates use the canonical finite base/orbit append.
-/

open Set Metric

namespace GlobalEmbedding.Paper

/-- An invariant complex open set containing a whole real torus orbit contains one common
complex base neighborhood times a uniform imaginary torus strip.

Source: Proposition `prop:collar`, proof lines 530–534. The fundamental real cube is compact
and its actual embedding at the fixed real base lies in the open domain. Choose a positive
thickening contained in the domain. Subtract the integer parts of the real orbit coordinates
of any candidate complex point. Its real fractional parts give a point of that compact cube.
The complex distance to it is controlled by the base deviations and the imaginary orbit
coordinates. Thus the reduced point lies in the thickening. Actual integer-domain invariance
returns the original point. Empty base/orbit dimensions use the same construction. -/
theorem collar_torus_complex_strip_neighborhood {b a : ℕ}
    (U : Set (Fin (b + a) → ℂ)) (hU : IsOpen U) (p₀ : Fin b → ℝ)
    (hbase : ∀ y : Fin a → ℝ,
      Fin.append (fun i ↦ (p₀ i : ℂ)) (fun j ↦ (y j : ℂ)) ∈ U)
    (hinv : ∀ (z : Fin (b + a) → ℂ) (t : Fin a → ℤ),
      z + Fin.append (fun _ : Fin b ↦ (0 : ℂ)) (fun j ↦ (t j : ℂ)) ∈ U ↔ z ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin (b + a) → ℂ,
      (∀ i : Fin b, ‖z (Fin.castAdd a i) - (p₀ i : ℂ)‖ < ε) →
      (∀ j : Fin a, |(z (Fin.natAdd b j)).im| < ε) → z ∈ U := by
  let φ (y : Fin a → ℝ) : Fin (b + a) → ℂ :=
    Fin.append (fun i ↦ (p₀ i : ℂ)) (fun j ↦ (y j : ℂ))
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [φ, Fin.append_left]
      fun_prop
    · intro j
      simp only [φ, Fin.append_right]
      fun_prop
  let K := φ '' Icc (0 : Fin a → ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hφ
  have hKU : K ⊆ U := by
    rintro _ ⟨y, _, rfl⟩
    exact hbase y
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨ε, hε, ?_⟩
  intro z hp him
  let t : Fin a → ℤ := fun j ↦ ⌊(z (Fin.natAdd b j)).re⌋
  let y : Fin a → ℝ := fun j ↦ Int.fract (z (Fin.natAdd b j)).re
  let v : Fin (b + a) → ℂ := Fin.append (fun _ : Fin b ↦ 0) (fun j ↦ (t j : ℂ))
  have hy : y ∈ Icc (0 : Fin a → ℝ) 1 :=
    ⟨fun _ ↦ Int.fract_nonneg _, fun _ ↦ (Int.fract_lt_one _).le⟩
  have hmem : φ y ∈ K := ⟨y, hy, rfl⟩
  have hdist : dist (z - v) (φ y) < ε := by
    rw [dist_eq_norm, pi_norm_lt_iff hε]
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Pi.sub_apply, v, φ, Fin.append_left, sub_zero] using hp j
    · intro j
      simp only [Pi.sub_apply, v, φ, Fin.append_right]
      have hfract : y j + (t j : ℝ) = (z (Fin.natAdd b j)).re :=
        Int.fract_add_floor _
      have he : z (Fin.natAdd b j) - (t j : ℂ) - (y j : ℂ) =
          ((z (Fin.natAdd b j)).im : ℂ) * Complex.I := by
        have htj : (t j : ℂ) = ((t j : ℝ) : ℂ) := by norm_cast
        rw [htj]
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self]
          linarith
        · simp
      rw [he, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      exact him j
  have hzU := hεU (mem_thickening_iff.mpr ⟨_, hmem, hdist⟩)
  have he : z - v + v = z := sub_add_cancel z v
  exact he ▸ (hinv (z - v) t).mpr hzU

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_torus_complex_strip_neighborhood
