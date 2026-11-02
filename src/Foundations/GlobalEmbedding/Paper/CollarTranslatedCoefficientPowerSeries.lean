import GlobalEmbedding.Paper.CollarCoefficientHolderPowerSeries
import Mathlib.Analysis.Analytic.Composition

/-!
# Actual analytic coefficient slices with a complex orbit translation parameter

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The source family evaluates its coefficients at (p,y+α). This is an
actual finite-dimensional complex linear pullback before the proved Hölder-valued series.
-/

open Set WithLp
open scoped ContDiff NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- Joint complex base/translation parameters construct actual translated coefficient power
series in the actual complex little Hölder norm.

Source: Proposition `prop:collar`, proof lines 530–534. The finite-dimensional complex linear
map ((z,w)↦(πz,w+Az)) combines the base parameter and the complex translation. Pull back the
actual source invariant open domain and its analytic coefficient along that map. Integer
spatial shifts commute with the map, so the pulled-back domain and coefficients are genuinely
periodic inside that domain. Apply the proved actual Hölder coefficient power-series theorem.
Its exact lift identity is precisely g(πz,y+Az), including the complex translation parameter.
No assumed Holder-valued holomorphic family or multiplier analyticity is used.
-/
theorem collar_translated_coefficient_power_series {b c a N k : ℕ} {α : ℝ}
    (g : (EuclideanSpace ℂ (Fin c) × EuclideanSpace ℂ (Fin a)) →
      EuclideanSpace ℂ (Fin N))
    (U : Set (EuclideanSpace ℂ (Fin c) × EuclideanSpace ℂ (Fin a)))
    (hU : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hinv : ∀ (w : EuclideanSpace ℂ (Fin c) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ), w + (0, toLp 2 (fun i ↦ (t i : ℂ))) ∈ U ↔ w ∈ U)
    (hperiodic : ∀ (w : EuclideanSpace ℂ (Fin c) × EuclideanSpace ℂ (Fin a)),
      w ∈ U → ∀ (t : Fin a → ℤ), g (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) = g w)
    (π : EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c))
    (A : EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin a))
    (z₀ : EuclideanSpace ℂ (Fin b))
    (hslice : ∀ x : EuclideanSpace ℝ (Fin a),
      (π z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)) + A z₀) ∈ U)
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
            g (π (z₀ + z), toLp 2 (fun i : Fin a ↦ (y i : ℂ)) + A (z₀ + z))) := by
  let L : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →L[ℂ]
      (EuclideanSpace ℂ (Fin c) × EuclideanSpace ℂ (Fin a)) :=
    (π.comp (ContinuousLinearMap.fst ℂ _ _)).prod
      (ContinuousLinearMap.snd ℂ _ _ + A.comp (ContinuousLinearMap.fst ℂ _ _))
  have hL (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) :
      L w = (π w.1, w.2 + A w.1) := rfl
  have hshift (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ) : L (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) =
        L w + (0, toLp 2 (fun i ↦ (t i : ℂ))) := by
    simp only [hL, Prod.fst_add, Prod.snd_add, add_zero]
    ext i <;> simp [add_assoc, add_left_comm, add_comm]
  let V := L ⁻¹' U
  have hV : IsOpen V := hU.preimage L.continuous
  have hVG : AnalyticOnNhd ℂ (g ∘ L) V :=
    hg.comp (fun x _ ↦ L.analyticAt x) (fun _ hx ↦ hx)
  have hVs : ∀ x : EuclideanSpace ℝ (Fin a),
      (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) ∈ V := by
    intro x
    exact hslice x
  have hVi : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ), w + (0, toLp 2 (fun i ↦ (t i : ℂ))) ∈ V ↔ w ∈ V := by
    intro w t
    change L (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) ∈ U ↔ L w ∈ U
    rw [hshift]
    exact hinv (L w) t
  have hVp : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)),
      w ∈ V → ∀ (t : Fin a → ℤ), (g ∘ L) (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) =
        (g ∘ L) w := by
    intro w hw t
    change g (L (w + (0, toLp 2 (fun i ↦ (t i : ℂ))))) = g (L w)
    rw [hshift]
    exact hperiodic (L w) hw t
  obtain ⟨ρ, hρ, F, p, hFp, hsm, hpc, hbound, hF⟩ := collar_coefficient_holder_power_series
    (k := k) (α := α) (g ∘ L) V hV z₀ hVs hVG hVi hVp hα D hdiam
  refine ⟨ρ, hρ, F, p, hFp, hsm, hpc, hbound, ?_⟩
  intro z hz y
  simpa only [Function.comp_apply, hL] using hF z hz y

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_translated_coefficient_power_series
