import GlobalEmbedding.Paper.PeriodicCAlphaFunction

/-!
# The real periodic Hölder norm formula

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-calpha-norm`.
-/

open Set WithLp
open scoped BigOperators

namespace GlobalEmbedding.Paper

/-- The sum of the derivative suprema through order k and the top flat-torus Hölder seminorm.

Each supremum is a real supremum. Finiteness is part of the actual carrier, and no extended
real value is converted to a real number. In torus dimension zero the Hölder-quotient set is
empty, and its real supremum is zero. This declaration defines only the formula; its norm
laws and resulting normed-space data are separate obligations.
Source: `lem:balanced`, proof, line 382, ambient Hölder-norm expansion. -/
noncomputable def periodicCAlphaNorm {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
    (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j f.toFun x‖}) +
    sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
      let d := dist
        (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
      0 < d ∧ r = ‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ / d ^ α}

#print axioms periodicCAlphaNorm

end GlobalEmbedding.Paper
