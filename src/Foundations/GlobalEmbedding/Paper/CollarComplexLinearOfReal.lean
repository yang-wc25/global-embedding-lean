import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Upgrading real continuous linear maps which commute with multiplication by i

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534, bounded complexification of the real correction operator. This elementary
scalar-extension step applies to arbitrary complex normed spaces, including Banach domains.
-/

namespace GlobalEmbedding.Paper

/-- A real continuous linear map between complex normed spaces is complex linear if it commutes
with multiplication by `I`. The resulting complex operator has the same real restriction and norm.

Source: Proposition `prop:collar`, proof lines 530–534, real-operator complexification.
Write each complex scalar as `a+I*b` with real a,b. Real linearity and commutation with I then
prove compatibility with that scalar. The same underlying continuous function defines the complex
continuous linear map. Restricting back to real scalars recovers the original map, and the operator
norm is unchanged because the source and target norms and underlying function are unchanged.
-/
theorem collar_complex_linear_of_real
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (L : E →L[ℝ] F) (hI : ∀ x : E, L (Complex.I • x) = Complex.I • L x) :
    ∃ C : E →L[ℂ] F, C.restrictScalars ℝ = L ∧ ‖C‖ = ‖L‖ := by
  have hsmul (c : ℂ) (x : E) : L (c • x) = c • L x := by
    rw [← Complex.re_add_im c]
    change L (((algebraMap ℝ ℂ c.re) + (algebraMap ℝ ℂ c.im) * Complex.I) • x) =
      ((algebraMap ℝ ℂ c.re) + (algebraMap ℝ ℂ c.im) * Complex.I) • L x
    simp only [add_smul, mul_smul, IsScalarTower.algebraMap_smul ℂ, L.map_add, L.map_smul, hI]
  let C : E →L[ℂ] F :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := hsmul
      cont := L.continuous }
  have hrestrict : C.restrictScalars ℝ = L := by ext x; rfl
  refine ⟨C, hrestrict, ?_⟩
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ) C, hrestrict]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_linear_of_real
