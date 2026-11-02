import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Abel

/-!
# Coordinate identities for a complex Banach real form

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The unique real/imaginary decomposition gives the coordinate identities
needed to construct the bounded complexification of the real bilinear correction operator.
-/

namespace GlobalEmbedding.Paper

/-- Unique real/imaginary decomposition forces the usual coordinate identities on multiplication
by I and on embedded real vectors.

Source: Proposition `prop:collar`, proof lines 530–534, real-form complexification.
An embedded real vector ιu has representation (u,0), so uniqueness recovers its coordinates.
Multiplying the representation x=ι(r x)+I•ι(s x) by I gives the representation
I•x=ι(−s x)+I•ι(r x), since I²=−1. Uniqueness identifies those coordinates with r(Ix),s(Ix).
Thus the required compatibility identities follow from the real-form hypothesis itself.
-/
theorem collar_real_form_coordinate_identities
    {E U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (ι : U →L[ℝ] E) (r s : E →L[ℝ] U)
    (hdecomp : ∀ x : E, ι (r x) + Complex.I • ι (s x) = x)
    (hunique : ∀ (x : E) (u v : U), ι u + Complex.I • ι v = x →
      u = r x ∧ v = s x) :
    (∀ x : E, r (Complex.I • x) = -s x) ∧
      (∀ x : E, s (Complex.I • x) = r x) ∧
      (∀ u : U, r (ι u) = u) ∧ (∀ u : U, s (ι u) = 0) := by
  have hI (x : E) : ι (-s x) + Complex.I • ι (r x) = Complex.I • x := by
    conv_rhs => rw [← hdecomp x]
    simp only [map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  have hreal (u : U) : u = r (ι u) ∧ (0 : U) = s (ι u) :=
    hunique (ι u) u 0 (by simp)
  exact ⟨fun x ↦ (hunique _ _ _ (hI x)).1.symm,
    fun x ↦ (hunique _ _ _ (hI x)).2.symm,
    fun u ↦ (hreal u).1.symm, fun u ↦ (hreal u).2.symm⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_real_form_coordinate_identities
