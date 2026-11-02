import GlobalEmbedding.Paper.EuclideanCoordinateWordDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Actual coordinate second partials commute on genuine C2 lifts

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1), lines 388–399.
DAG node: `euclidean-coordinate-second-partials-commute`.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Genuine C2 coordinate second partial derivatives commute in the actual word realization.

Differentiate evaluation of the actual first derivative at a constant coordinate vector.
This is the actual second Frechet derivative on the two coordinate vectors. Mathlib's
C2 Schwarz theorem exchanges these vectors, giving the stated order-independence.
Source: commuting coordinate derivatives in the proof after (4.1). -/
theorem euclideanCoordinateWordDerivative_pair_commute {a N : ℕ}
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)) (hf : ContDiff ℝ 2 f)
    (i j : Fin a) (x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative [i, j] f x =
      euclideanCoordinateWordDerivative [j, i] f x := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2.differentiable
      (by norm_num)
  have heval (u : EuclideanSpace ℝ (Fin a)) :
      fderiv ℝ (fun y ↦ fderiv ℝ f y u) x = (fderiv ℝ (fderiv ℝ f) x).flip u := by
    have h := (hdf x).hasFDerivAt.clm_apply (hasFDerivAt_const u x)
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using h.fderiv
  simp only [euclideanCoordinateWordDerivative, heval]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

#print axioms euclideanCoordinateWordDerivative_pair_commute

end GlobalEmbedding.Paper
