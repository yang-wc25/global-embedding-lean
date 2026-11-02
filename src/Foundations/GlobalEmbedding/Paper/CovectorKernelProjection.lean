import Mathlib.Analysis.Normed.Operator.Bilinear

namespace GlobalEmbedding.Paper

/-- The actual rank-one projection onto a covector kernel along a chosen vector.
The separate properties theorem applies where `ξ v ≠ 0`.
Source: `defn:phase`, local variation of actual covector kernels. -/
noncomputable def covectorKernelProjection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (ξ : E →L[ℝ] ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ξ.smulRight ((ξ v)⁻¹ • v)

end GlobalEmbedding.Paper
