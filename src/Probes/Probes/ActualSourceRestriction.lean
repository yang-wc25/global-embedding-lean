import Probes.ActualPairedProbeSource

/-!
# Native source jets after freezing an auxiliary parameter

The original mode solver differentiates only in its spatial variable. This
file derives those exact native jets by restricting the joint derivative to
the isometric spatial inclusion. Consequently primitive joint source budgets
pass to the actual reconstruction input without extra parameter derivatives,
changed norms, or a new source-budget hypothesis.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Exact arbitrary-order restriction of a local joint jet to a fixed
parameter slice, in the original product norm. -/
theorem iteratedFDeriv_fixed_parameter_slice
    (f : P × X → Y) (O : Set (P × X)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (p : P) (x : X) (hx : (p, x) ∈ O) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y ↦ f (p, y)) x =
      (iteratedFDeriv ℝ n f (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ P X) := by
  let L : X →L[ℝ] P × X := ContinuousLinearMap.inr ℝ P X
  let g : P × X → Y := fun z ↦ f ((p, 0) + z)
  let U : Set (P × X) := (fun z ↦ (p, 0) + z) ⁻¹' O
  have hU : IsOpen U := hO.preimage (continuous_const.add continuous_id)
  have hg : ContDiffOn ℝ ∞ g U :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (by intro z hz; exact hz)
  have hLU : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hxu : L x ∈ U := by simpa [U, L] using hx
  have hj := L.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hLU.uniqueDiffOn hxu
    (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hLU hxu,
    iteratedFDerivWithin_of_isOpen n hU hxu] at hj
  have he : g ∘ L = fun y ↦ f (p, y) := by funext y; simp [g, L]
  rw [he] at hj
  change iteratedFDeriv ℝ n (fun y ↦ f (p, y)) x = _
  rw [hj]
  congr 1
  simpa [g, L] using iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) n (p, (0 : X)) (L x)

/-- Freezing a parameter never increases any native spatial jet norm. -/
theorem norm_iteratedFDeriv_fixed_parameter_slice_le
    (f : P × X → Y) (O : Set (P × X)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (p : P) (x : X) (hx : (p, x) ∈ O) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f (p, y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (p, x)‖ := by
  rw [iteratedFDeriv_fixed_parameter_slice f O hO hf p x hx n]
  have hL : ‖ContinuousLinearMap.inr ℝ P X‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp
  apply ((iteratedFDeriv ℝ n f (p, x)).norm_compContinuousLinearMap_le _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hL)

/-- A true joint slow-jet budget supplies the source-only native budget on
every slice, with exactly the same constant and derivative order. -/
theorem fixed_parameter_slice_weighted_jets
    (f : P × X → Y) (O : Set (P × X)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (j : ℕ) (ell K : ℝ) (hell : 0 ≤ ell)
    (hb : ∀ n ≤ j, ∀ z ∈ O, ell ^ n * ‖iteratedFDeriv ℝ n f z‖ ≤ K) (p : P) :
    ContDiffOn ℝ ∞ (fun x ↦ f (p, x)) ((fun x ↦ (p, x)) ⁻¹' O) ∧
    ∀ n ≤ j, ∀ x, (p, x) ∈ O →
      ell ^ n * ‖iteratedFDeriv ℝ n (fun y ↦ f (p, y)) x‖ ≤ K := by
  refine ⟨hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (by intro x hx; exact hx), ?_⟩
  intro n hn x hx
  exact (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_fixed_parameter_slice_le f O hO hf p x hx n) (pow_nonneg hell n)).trans
    (hb n hn (p, x) hx)

#print axioms iteratedFDeriv_fixed_parameter_slice
#print axioms fixed_parameter_slice_weighted_jets
end GlobalEmbedding.Offline
