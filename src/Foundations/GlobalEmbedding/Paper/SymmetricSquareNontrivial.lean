import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace GlobalEmbedding.Paper

/-- A nonzero real inner product space has a nonzero actual symmetric square.

Proof: descend the symmetric bilinear square of inner product with a nonzero v.
Its value on v⊙v is positive, so that actual quotient element is nonzero.
Source: `defn:phase`, nonempty unit spheres in symmetric squares of hyperplanes. -/
theorem symmetric_square_nontrivial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] :
    Nontrivial (SymmetricSquare E) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let l : E →ₗ[ℝ] ℝ := (innerSL ℝ v).toLinearMap
  let β : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := l.smulRight l
  have hβ : ∀ x y, β x y = β y x := by
    intro x y
    change l x * l y = l y * l x
    ring
  have hprod : symmetricSquareProduct E v v ≠ 0 := by
    intro he
    have h := congrArg (symmetricBilinearDescend β hβ) he
    rw [symmetricBilinearDescend_product, map_zero] at h
    have hl : 0 < l v := by
      change 0 < inner ℝ v v
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hv)
    change l v * l v = 0 at h
    exact (ne_of_gt (mul_pos hl hl)) h
  exact nontrivial_of_ne _ _ hprod

end GlobalEmbedding.Paper
