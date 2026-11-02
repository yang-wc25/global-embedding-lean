import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace GlobalEmbedding.Paper

/-- In dimension at least two the actual kernel of every real covector is
nontrivial. Source: `defn:phase`, hyperplane minimum singular norm.

Proof: rank-nullity and rank(range xi)≤dim ℝ=1 give positive kernel dimension. -/
theorem covector_kernel_nontrivial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 ≤ Module.finrank ℝ E) (ξ : E →L[ℝ] ℝ) : Nontrivial ξ.ker := by
  have he := ξ.ker.finrank_quotient_add_finrank
  rw [ξ.toLinearMap.quotKerEquivRange.finrank_eq] at he
  have hr : Module.finrank ℝ ξ.toLinearMap.range ≤ 1 := by
    simpa using Submodule.finrank_le ξ.toLinearMap.range
  have hk : 0 < Module.finrank ℝ ξ.ker := by
    have hreal : Module.finrank ℝ ℝ = 1 := by simp
    omega
  exact Module.nontrivial_of_finrank_pos hk

end GlobalEmbedding.Paper
