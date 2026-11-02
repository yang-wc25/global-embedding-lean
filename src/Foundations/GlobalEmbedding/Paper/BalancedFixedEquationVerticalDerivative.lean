import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Linearization of the quadratic fixed-point equation

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 418–425. DAG node: `balanced-fixed-equation-vertical-derivative`.
-/

namespace GlobalEmbedding.Paper

/-- The derivative in the unknown of a symmetric quadratic fixed-point equation is
`I-2AQ(x,·)`.

Proof: the bilinear derivative of `Q(y,y)` is `Q(x,·)+Q(·,x)`. Symmetry identifies the
summands. Composing with A and subtracting from the identity gives the stated derivative.
Source: proof of `lem:balanced`, lines 418–425. -/
theorem balanced_fixed_equation_hasFDerivAt {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Q : X →L[ℝ] X →L[ℝ] Y) (hQ : ∀ x y, Q x y = Q y x)
    (A : Y →L[ℝ] X) (f x : X) :
    HasFDerivAt (fun y ↦ y - f - A (Q y y))
      (ContinuousLinearMap.id ℝ X - (2 : ℝ) • A.comp (Q x)) x := by
  have hq := Q.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  have haq := A.hasFDerivAt.comp x hq
  convert ((hasFDerivAt_id x).sub_const f).sub haq using 1 <;>
    (ext y; simp [ContinuousLinearMap.precompR, hQ y x, two_smul])


#print axioms balanced_fixed_equation_hasFDerivAt

end GlobalEmbedding.Paper
