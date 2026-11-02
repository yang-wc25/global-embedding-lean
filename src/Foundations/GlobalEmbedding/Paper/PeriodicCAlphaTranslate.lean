import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaGlobalJetBound
import GlobalEmbedding.Paper.PeriodicFlatTranslationDistance
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual ambient periodic Hölder translations

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 382–418. DAG node: `balanced-holder-raw-translation`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Translation of an actual periodic Hölder element by a Euclidean lift of a torus shift.

The underlying function is exactly x↦f(x+h). Integer periodicity and C^k regularity persist.
The actual global jet bounds give the derivative finiteness witnesses, and invariance of the
actual flat torus metric preserves the given Hölder quotient bound. No assumed translation
operator or new carrier is used. Source: `lem:balanced`, periodic translation argument. -/
noncomputable def periodicCAlphaTranslate {a N k : ℕ} {α : ℝ}
    (h : EuclideanSpace ℝ (Fin a)) (f : PeriodicCAlphaFunction a N k α) :
    PeriodicCAlphaFunction a N k α where
  toFun x := f.toFun (x + h)
  periodic := by
    intro x n
    rw [show x + toLp 2 (fun i ↦ (n i : ℝ)) + h =
      (x + h) + toLp 2 (fun i ↦ (n i : ℝ)) by abel]
    exact f.periodic (x + h) n
  contDiff := f.contDiff.comp (contDiff_id.add contDiff_const)
  derivative_bounded := by
    intro j hj
    refine ⟨periodicCAlphaNorm f, ?_⟩
    intro x hx
    rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) j h x]
    exact periodicCAlpha_global_jet_bound f j hj (x + h)
  holder_bounded := by
    obtain ⟨C, hC⟩ := f.holder_bounded
    refine ⟨C, ?_⟩
    intro x y d hd
    rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) k h x,
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) k h y]
    have hdist := periodic_flat_translation_distance x y h
    have hd' : 0 < dist (toLp 2 (fun i : Fin a ↦ ((x + h) i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ ((y + h) i : AddCircle (1 : ℝ)))) := by
      rw [hdist]
      exact hd
    simpa only [hdist] using hC (x + h) (y + h) hd'

#print axioms periodicCAlphaTranslate

end GlobalEmbedding.Paper
