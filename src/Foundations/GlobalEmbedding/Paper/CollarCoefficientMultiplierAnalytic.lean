import GlobalEmbedding.Paper.BalancedHolderMultiplicationBounded
import GlobalEmbedding.Paper.HilbertSchmidtCoordinateEvaluationFormula
import GlobalEmbedding.Paper.CollarHolderPointwiseMultiplier
import GlobalEmbedding.Paper.CollarComplexHilbertSchmidtEvaluation

/-!
# Actual analytic complex matrix multipliers on the original little Hölder spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. DAG node: `collar-coefficient-multiplier-analytic`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- The actual matrix-valued complex little Hölder coefficient determines a bounded complex
linear multiplier, and the coefficient-to-operator map is bounded complex linear. Every actual
analytic coefficient family therefore gives an operator-norm analytic multiplier family.

Source: Proposition `prop:collar`, proof lines 530–534. Use the proved real little-space
Hilbert–Schmidt multiplication theorem, with no assumed product data. Its canonical coordinate
formula agrees with the actual complex value product on real inputs. Complexify the actual
bounded real product using the genuine closed real forms, then identify its pointwise action
on all complex functions. Compose this actual coefficient CLM with the analytic family.
The coefficient norm is the original Euclidean Hilbert–Schmidt norm, not an operator norm
substituted for it. Either empty value dimension is allowed. -/
theorem collar_coefficient_multiplier_analytic
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {a M N k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (A : Z → CollarComplexHolderSpace a (N * M) k α) (z₀ : Z)
    (hA : AnalyticAt ℂ A z₀) :
    ∃ C : CollarComplexHolderSpace a (N * M) k α →L[ℂ]
        CollarComplexHolderSpace a M k α →L[ℂ] CollarComplexHolderSpace a N k α,
      (∀ f u (y : EuclideanSpace ℝ (Fin a)) (i : Fin N),
        collarComplexHolderFunction (C f u) y i =
          ∑ j : Fin M, collarComplexHolderFunction f y (finProdFinEquiv (i, j)) *
            collarComplexHolderFunction u y j) ∧
      AnalyticAt ℂ (fun z ↦ C (A z)) z₀ := by
  obtain ⟨_, _, Q, hQ, _⟩ :=
    balanced_holder_multiplication_bounded (a := a) (M := M) (N := N) (k := k) hα0 hα1
  have hreal (f : LittlePeriodicCAlphaFunction a (N * M) k α)
      (u : LittlePeriodicCAlphaFunction a M k α) (y : EuclideanSpace ℝ (Fin a)) :
      toLp 2 (fun i : Fin N ↦ ((Q f u : PeriodicCAlphaFunction a N k α).toFun y i : ℂ)) =
        collarComplexHilbertSchmidtEvaluation M N
          (toLp 2 (fun r ↦ ((f : PeriodicCAlphaFunction a (N * M) k α).toFun y r : ℂ)))
          (toLp 2 (fun j ↦ ((u : PeriodicCAlphaFunction a M k α).toFun y j : ℂ))) := by
    rw [collar_complex_hilbert_schmidt_real_formula]
    ext i
    change ((Q f u).val.toFun y i : ℂ) = _
    rw [hQ]
    rw [hilbertSchmidt_coordinate_evaluation_formula]
  obtain ⟨C, hC, hCA⟩ := collar_holder_pointwise_multiplier Q
    (collarComplexHilbertSchmidtEvaluation M N) hreal A z₀ hA
  refine ⟨C, ?_, hCA⟩
  intro f u y i
  rw [hC, collar_complex_hilbert_schmidt_evaluation_formula]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_coefficient_multiplier_analytic
