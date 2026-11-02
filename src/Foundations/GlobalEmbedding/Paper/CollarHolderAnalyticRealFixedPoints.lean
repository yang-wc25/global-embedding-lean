import GlobalEmbedding.Paper.CollarComplexHolderClosedRealForm
import GlobalEmbedding.Paper.CollarCoefficientMultiplierAnalytic
import GlobalEmbedding.Paper.CollarAnalyticRealFixedPoints

/-!
# Actual Hölder coefficient products and their analytic real fixed points

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2), proof lines 524–534.
-/

open Set Filter
open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Actual analytic matrix and forcing Hölder coefficients construct the actual multiplier
and forcing product analyticity, and a real invariant contraction ball gives an actual
analytic fixed point for the original quadratic right-hand side.

Source: Proposition `prop:collar`, equation (5.2), proof lines 524–534. Construct the actual
bounded complex matrix multiplier from the proved real Hilbert–Schmidt product. Its complex
CLM composition with the actual matrix family is operator-norm analytic. Bounded bilinear
operator evaluation gives genuine analyticity of its product with half the forcing. The actual
closed real Hölder submodule, its coordinates and original norm identification are constructed
by the real-form theorem. Rewrite pointwise reality as membership in that actual submodule,
and use complex linearity to split the original right-hand side into its analytic forcing and
fixed bounded quadratic part. The proved analytic real fixed-points theorem constructs the
actual branch and its real-ball uniqueness, including radius zero and boundary fixed points.
The source Q construction and real invariant-ball contraction are explicit separate obligations;
no multiplier, operator analyticity or actual real-form data is an extra assumption. -/
theorem collar_holder_analytic_real_fixed_points
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℂ Z]
    [IsScalarTower ℝ ℂ Z] [CompleteSpace Z]
    {a M N k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (P : Submodule ℝ Z) (p₀ : P)
    (A : Z → CollarComplexHolderSpace a (N * M) k α)
    (H : Z → CollarComplexHolderSpace a M k α)
    (B : CollarComplexHolderSpace a N k α →L[ℂ]
      CollarComplexHolderSpace a N k α →L[ℂ] CollarComplexHolderSpace a M k α)
    (hA : AnalyticAt ℂ A (p₀ : Z)) (hH : AnalyticAt ℂ H (p₀ : Z)) :
    ∃ C : CollarComplexHolderSpace a (N * M) k α →L[ℂ]
        CollarComplexHolderSpace a M k α →L[ℂ] CollarComplexHolderSpace a N k α,
      (∀ coeff u (y : EuclideanSpace ℝ (Fin a)) (i : Fin N),
        collarComplexHolderFunction (C coeff u) y i =
          ∑ j : Fin M, collarComplexHolderFunction coeff y (finProdFinEquiv (i, j)) *
            collarComplexHolderFunction u y j) ∧
      AnalyticAt ℂ (fun z ↦ C (A z)) (p₀ : Z) ∧
      AnalyticAt ℂ (fun z ↦ C (A z) ((1 / 2 : ℂ) • H z)) (p₀ : Z) ∧
      ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (q : ℝ≥0), (q : ℝ) < 1 →
        (∀ᶠ p : P in 𝓝 p₀,
          let S : Set (CollarComplexHolderSpace a N k α) :=
            {x | (∀ y i, (collarComplexHolderFunction x y i).im = 0) ∧ ‖x‖ ≤ ρ}
          let Φ := fun x ↦ C (A (p : Z)) ((1 / 2 : ℂ) • H (p : Z) + B x x)
          Set.MapsTo Φ S S ∧ LipschitzOnWith q Φ S) →
        ∃ ψ : Z → CollarComplexHolderSpace a N k α, AnalyticAt ℂ ψ (p₀ : Z) ∧
          ∀ᶠ p : P in 𝓝 p₀,
            let S : Set (CollarComplexHolderSpace a N k α) :=
              {x | (∀ y i, (collarComplexHolderFunction x y i).im = 0) ∧ ‖x‖ ≤ ρ}
            let Φ := fun x ↦ C (A (p : Z)) ((1 / 2 : ℂ) • H (p : Z) + B x x)
            ψ (p : Z) ∈ S ∧ Φ (ψ (p : Z)) = ψ (p : Z) ∧
              ∀ x ∈ S, Φ x = x ↔ ψ (p : Z) = x := by
  obtain ⟨C, hC, hCA⟩ := collar_coefficient_multiplier_analytic hα0 hα1 A (p₀ : Z) hA
  have hhalf : AnalyticAt ℂ (fun z ↦ (1 / 2 : ℂ) • H z) (p₀ : Z) :=
    hH.const_smul (c := (1 / 2 : ℂ))
  have hforcing : AnalyticAt ℂ (fun z ↦ C (A z) ((1 / 2 : ℂ) • H z)) (p₀ : Z) :=
    ((ContinuousLinearMap.apply ℂ (CollarComplexHolderSpace a N k α)).analyticAt_bilinear
      ((1 / 2 : ℂ) • H (p₀ : Z), C (A (p₀ : Z)))).comp₂ hhalf hCA
  refine ⟨C, hC, hCA, hforcing, ?_⟩
  intro ρ hρ q hq hnear
  obtain ⟨R, hR, _, r, s, _, hmem, hd, _, _⟩ :=
    collar_complex_holder_closed_real_form (a := a) (N := N) (k := k) (α := α)
  let f : Z → CollarComplexHolderSpace a N k α :=
    fun z ↦ C (A z) ((1 / 2 : ℂ) • H z)
  let L : Z → CollarComplexHolderSpace a M k α →L[ℂ]
      CollarComplexHolderSpace a N k α := fun z ↦ C (A z)
  let S : Set (CollarComplexHolderSpace a N k α) :=
    {x | (∀ y i, (collarComplexHolderFunction x y i).im = 0) ∧ ‖x‖ ≤ ρ}
  let Φ : Z → CollarComplexHolderSpace a N k α → CollarComplexHolderSpace a N k α :=
    fun z x ↦ C (A z) ((1 / 2 : ℂ) • H z + B x x)
  have hS : {x : CollarComplexHolderSpace a N k α | x ∈ R ∧ ‖x‖ ≤ ρ} = S := by
    ext x
    change (x ∈ R ∧ ‖x‖ ≤ ρ) ↔
      ((∀ y i, (collarComplexHolderFunction x y i).im = 0) ∧ ‖x‖ ≤ ρ)
    rw [hmem]
  have hΦ (z : Z) (x : CollarComplexHolderSpace a N k α) :
      f z + L z (B x x) = Φ z x := by
    exact (C (A z)).map_add _ _ |>.symm
  have hnearR : ∀ᶠ p : P in 𝓝 p₀,
      let S' : Set (CollarComplexHolderSpace a N k α) := {x | x ∈ R ∧ ‖x‖ ≤ ρ}
      let Φ' := fun x ↦ f (p : Z) + L (p : Z) (B x x)
      Set.MapsTo Φ' S' S' ∧ LipschitzOnWith q Φ' S' := by
    simpa only [hS, hΦ] using hnear
  obtain ⟨ψ, hψ, hψnear⟩ := collar_analytic_real_fixed_points
    P R hR r s hd f L B p₀ ρ hρ q hq hforcing hCA hnearR
  refine ⟨ψ, hψ, ?_⟩
  simpa only [hS, hΦ] using hψnear

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_analytic_real_fixed_points
