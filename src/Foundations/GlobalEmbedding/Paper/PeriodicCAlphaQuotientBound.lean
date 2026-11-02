import GlobalEmbedding.Paper.PeriodicCAlphaNorm
import GlobalEmbedding.Paper.PeriodicCAlphaSupremumBounds

/-!
# Pointwise top Hölder quotient control

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-top-quotient-bound`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Every top derivative Hölder quotient at a positive flat-torus distance is at most the
actual periodic Hölder norm formula.

Proof: the finite Hölder supremum bounds each member of its quotient set. The remaining
finite derivative-supremum sum is nonnegative. Source: `lem:balanced`, norm expansion. -/
theorem periodicCAlpha_quotient_bound {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) (x y : EuclideanSpace ℝ (Fin a))
    (hd : 0 < dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
      (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))) :
    ‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ /
        dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ^ α ≤
      periodicCAlphaNorm f := by
  apply (le_csSup (periodicCAlpha_supremum_bounds f).2 ⟨x, y, hd, rfl⟩).trans
  apply le_add_of_nonneg_left
  apply Finset.sum_nonneg
  intro j hj
  apply Real.sSup_nonneg
  rintro r ⟨z, hz, rfl⟩
  exact norm_nonneg _

#print axioms periodicCAlpha_quotient_bound

end GlobalEmbedding.Paper
