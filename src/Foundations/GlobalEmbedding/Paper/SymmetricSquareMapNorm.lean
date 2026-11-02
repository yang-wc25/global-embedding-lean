import GlobalEmbedding.Paper.SymmetricSquareMap
import GlobalEmbedding.Paper.SymmetricSquareNorms

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

/-- The quotient norm of the induced map is bounded by the square of the operator norm.
Proof: choose representatives arbitrarily close to the quotient norm, apply the Hilbert
 tensor map estimate and the nonexpansiveness of the quotient map, then let the error vanish.
Source: the uniform transport estimate in `prop:initialization`. -/
theorem symmetricSquareMap_norm_le (f : E →L[ℝ] F) (z : SymmetricSquare E) :
    ‖symmetricSquareMap f z‖ ≤ ‖f‖ ^ 2 * ‖z‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hC : 0 ≤ ‖f‖ ^ 2 := sq_nonneg _
  obtain ⟨a, ha, hnorm⟩ := Submodule.Quotient.norm_mk_lt z
    (div_pos hε (by positivity : 0 < ‖f‖ ^ 2 + 1))
  rw [← ha, symmetricSquareMap_mk, ha]
  calc
    ‖(Submodule.Quotient.mk
        (TensorProduct.map f.toLinearMap f.toLinearMap a) : SymmetricSquare F)‖ ≤
        ‖TensorProduct.mapL f f a‖ := by
          simpa only [TensorProduct.mapL_apply] using
            (Submodule.Quotient.norm_mk_le (symmetricSquareRelations F)
              (TensorProduct.map f.toLinearMap f.toLinearMap a))
    _ ≤ ‖TensorProduct.mapL f f‖ * ‖a‖ := (TensorProduct.mapL f f).le_opNorm a
    _ ≤ (‖f‖ * ‖f‖) * ‖a‖ := by gcongr; exact TensorProduct.norm_mapL_le f f
    _ ≤ ‖f‖ ^ 2 * ‖z‖ + ε := by
      have h := mul_le_mul_of_nonneg_left hnorm.le hC
      have hdiv : ‖f‖ ^ 2 * (ε / (‖f‖ ^ 2 + 1)) ≤ ε := by
        have hp : 0 < ‖f‖ ^ 2 + 1 := by positivity
        calc
          ‖f‖ ^ 2 * (ε / (‖f‖ ^ 2 + 1)) ≤
              (‖f‖ ^ 2 + 1) * (ε / (‖f‖ ^ 2 + 1)) := by gcongr; linarith
          _ = ε := by field_simp
      nlinarith

end GlobalEmbedding.Paper
