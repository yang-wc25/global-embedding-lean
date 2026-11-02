import GlobalEmbedding.Paper.SchwartzLatticePartition
import GlobalEmbedding.Paper.SchwartzLatticeResolvent

open Module
open scoped SchwartzMap Laplacian ContDiff

namespace GlobalEmbedding.Paper

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

/-- Every actual smooth function periodic under an actual basis integer lattice has an
actual smooth periodic solution of Δu−u=f, in every finite real dimension. The covering
radius is proved from Mathlib's genuine floor/fract representative. A true compact
smooth partition converts the original periodic forcing into a Schwartz forcing;
periodizing its genuine Fourier-multiplier resolvent solves the original equation.
No desired PDE bijectivity or solvability is assumed. -/
theorem exists_smooth_basis_periodic_resolvent
    (b : Basis ι ℝ E) (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hperiod : ∀ (z : Submodule.span ℤ (Set.range b)) (x : E), f (x + z) = f x) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧
      (∀ (z : Submodule.span ℤ (Set.range b)) (x : E), u (x + z) = u x) ∧
      ∀ x, Laplacian.laplacian u x - u x = f x := by
  classical
  let L := Submodule.span ℤ (Set.range b)
  have : DiscreteTopology L := by dsimp [L]; infer_instance
  let R : ℝ := ∑ i, ‖b i‖
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcover (x : E) : ∃ z : L, ‖x + z‖ ≤ R := by
    refine ⟨-ZSpan.floor b x, ?_⟩
    simpa only [ZSpan.fract_apply, sub_eq_add_neg, Submodule.coe_neg] using
      ZSpan.norm_fract_le b x
  obtain ⟨χ, hχc, _, hχ⟩ := exists_schwartz_lattice_partition L hR hcover
  have hgc : HasCompactSupport (fun x => (-f x) * χ x) := by
    apply hχc.mono
    intro x hx
    change χ x ≠ 0
    intro hz
    apply hx
    change (-f x) * χ x = 0
    rw [hz, mul_zero]
  let g : 𝓢(E, ℝ) := hgc.toSchwartzMap (hf.neg.mul (χ.smooth (⊤ : ℕ∞)))
  have hg (x : E) : schwartzLatticePeriodization L g x = -f x := by
    change (∑' z : L, (-f (x + z)) * χ (x + z)) = -f x
    simp_rw [hperiod]
    rw [tsum_mul_left]
    change (-f x) * schwartzLatticePeriodization L χ x = -f x
    rw [hχ x, mul_one]
  obtain ⟨u, hu, hp, he⟩ := exists_smooth_lattice_periodic_resolvent L g
  refine ⟨u, hu, hp, fun x => ?_⟩
  have H := he x
  rw [hg] at H
  linarith

#print axioms exists_smooth_basis_periodic_resolvent

end GlobalEmbedding.Paper
