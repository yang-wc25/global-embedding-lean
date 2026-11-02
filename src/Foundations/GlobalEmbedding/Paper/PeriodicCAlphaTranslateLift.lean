import GlobalEmbedding.Paper.PeriodicCAlphaTranslate
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective

/-!
# Actual periodic Hölder translation is independent of the chosen torus lift

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-translation-lift-independence`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Euclidean shifts with the same actual flat torus class define the same raw translation.

Proof: equality of their quotient-circle coordinates makes each difference an integer.
Choose those integers, identify the difference with the integer lattice vector, and apply
the actual lift's periodicity. Source: the torus translation in the proof of `lem:balanced`. -/
theorem periodicCAlphaTranslate_lift_independent {a N k : ℕ} {α : ℝ}
    (h h' : EuclideanSpace ℝ (Fin a))
    (hh : toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ))) =
      toLp 2 (fun i : Fin a ↦ (h' i : AddCircle (1 : ℝ))))
    (f : PeriodicCAlphaFunction a N k α) :
    periodicCAlphaTranslate h f = periodicCAlphaTranslate h' f := by
  have hint (i : Fin a) : ∃ n : ℤ, (n : ℝ) = h' i - h i := by
    have hc : ((h' i - h i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr (congrArg (fun z ↦ z i) hh).symm
    simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hc
  choose n hn using hint
  have hh' : h' = h + toLp 2 (fun i ↦ (n i : ℝ)) := by
    ext i
    change h' i = h i + (n i : ℝ)
    rw [hn i]
    ring
  apply periodicCAlpha_toFun_injective
  funext x
  change f.toFun (x + h) = f.toFun (x + h')
  rw [hh', ← add_assoc]
  exact (f.periodic (x + h) n).symm

#print axioms periodicCAlphaTranslate_lift_independent

end GlobalEmbedding.Paper
