import GlobalEmbedding.Paper.PeriodicCAlphaTranslate
import GlobalEmbedding.Paper.PeriodicCAlphaDerivativeSup
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective

/-!
# Exact norm preservation of actual periodic Hölder translation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-translation-norm`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Translating an actual periodic Hölder lift preserves its exact original norm formula.

Proof: shifted derivative values are bounded by their original global periodic suprema.
Simultaneous shifts preserve the flat torus distance and hence the top quotient supremum.
This gives the upper inequality; applying it to the inverse shift gives the reverse.
Source: periodic Hölder translation in the proof of `lem:balanced`. -/
theorem periodicCAlphaTranslate_norm {a N k : ℕ} {α : ℝ}
    (h : EuclideanSpace ℝ (Fin a)) (f : PeriodicCAlphaFunction a N k α) :
    periodicCAlphaNorm (periodicCAlphaTranslate h f) = periodicCAlphaNorm f := by
  have hle (h : EuclideanSpace ℝ (Fin a)) (f : PeriodicCAlphaFunction a N k α) :
      periodicCAlphaNorm (periodicCAlphaTranslate h f) ≤ periodicCAlphaNorm f := by
    let D (u : PeriodicCAlphaFunction a N k α) (j : ℕ) :=
      sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
        (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j u.toFun x‖}
    let H (u : PeriodicCAlphaFunction a N k α) :=
      sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
        let d := dist
          (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
        0 < d ∧ r = ‖iteratedFDeriv ℝ k u.toFun x - iteratedFDeriv ℝ k u.toFun y‖ / d ^ α}
    have hD (j : ℕ) : 0 ≤ D f j := by
      apply Real.sSup_nonneg
      rintro r ⟨x, hx, rfl⟩
      exact norm_nonneg _
    have hH : 0 ≤ H f := by
      apply Real.sSup_nonneg
      rintro r ⟨x, y, hd, rfl⟩
      exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hd.le _)
    have hderiv (j : ℕ) (hj : j ≤ k) : D (periodicCAlphaTranslate h f) j ≤ D f j := by
      apply Real.sSup_le _ (hD j)
      rintro r ⟨x, hx, rfl⟩
      change ‖iteratedFDeriv ℝ j (fun z ↦ f.toFun (z + h)) x‖ ≤ D f j
      rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) j h x]
      exact periodicCAlpha_derivative_sup_global f j hj (x + h)
    have hholder : H (periodicCAlphaTranslate h f) ≤ H f := by
      apply Real.sSup_le _ hH
      rintro r ⟨x, y, hd, rfl⟩
      change ‖iteratedFDeriv ℝ k (fun z ↦ f.toFun (z + h)) x -
        iteratedFDeriv ℝ k (fun z ↦ f.toFun (z + h)) y‖ / _ ≤ H f
      rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) k h x,
        iteratedFDeriv_comp_add_right (𝕜 := ℝ) k h y]
      have hdist := periodic_flat_translation_distance x y h
      have hd' : 0 < dist (toLp 2 (fun i : Fin a ↦ ((x + h) i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ ((y + h) i : AddCircle (1 : ℝ)))) := by
        rw [hdist]
        exact hd
      have hq := le_csSup (periodicCAlpha_supremum_bounds f).2
        ⟨x + h, y + h, hd', rfl⟩
      simpa only [hdist] using hq
    change (∑ j ∈ Finset.range (k + 1), D (periodicCAlphaTranslate h f) j) +
      H (periodicCAlphaTranslate h f) ≤ (∑ j ∈ Finset.range (k + 1), D f j) + H f
    exact add_le_add (Finset.sum_le_sum (fun j hj ↦ hderiv j
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) hholder
  have hinv : periodicCAlphaTranslate (-h) (periodicCAlphaTranslate h f) = f := by
    apply periodicCAlpha_toFun_injective
    funext x
    change f.toFun (x + -h + h) = f.toFun x
    simp
  apply le_antisymm (hle h f)
  simpa only [hinv] using hle (-h) (periodicCAlphaTranslate h f)

#print axioms periodicCAlphaTranslate_norm

end GlobalEmbedding.Paper
