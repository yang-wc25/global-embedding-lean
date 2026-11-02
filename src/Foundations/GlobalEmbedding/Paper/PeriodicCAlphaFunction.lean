import GlobalEmbedding.Paper.PeriodicFlatTorusMinimum
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Raw periodic Hölder functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-periodic-calpha-functions`.

The torus distance below is the L2 product distance on period-one quotient circles, so it
is the flat Euclidean distance modulo the integer lattice. Iterated derivatives are taken
on the actual Euclidean lift and have a fixed multilinear-map codomain.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A raw periodic `C^{k,α}` function, for the paper's range `0 < α < 1`.

The data are an actual Euclidean lift, integer-lattice periodicity, classical `C^k` regularity,
and finite real bounds for every derivative supremum and the flat-torus top-order Hölder
quotient. No norm or completeness structure is asserted here. In torus dimension zero the
positive-distance condition has no instances, giving the prescribed zero Hölder contribution.
Source: `lem:balanced`, proof, line 382, little-Hölder ambient-carrier expansion. -/
structure PeriodicCAlphaFunction (a N k : ℕ) (α : ℝ) where
  toFun : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)
  periodic : ∀ (x : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ),
    toFun (x + toLp 2 (fun i ↦ (n i : ℝ))) = toFun x
  contDiff : ContDiff ℝ k toFun
  derivative_bounded : ∀ j ≤ k, ∃ C : ℝ,
    ∀ x : EuclideanSpace ℝ (Fin a), (∀ i, x i ∈ Icc (0 : ℝ) 1) →
      ‖iteratedFDeriv ℝ j toFun x‖ ≤ C
  holder_bounded : ∃ C : ℝ, ∀ x y : EuclideanSpace ℝ (Fin a),
    let d := dist
      (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
      (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
    0 < d → ‖iteratedFDeriv ℝ k toFun x - iteratedFDeriv ℝ k toFun y‖ / d ^ α ≤ C

#print axioms PeriodicCAlphaFunction

end GlobalEmbedding.Paper
