import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Order.Real

namespace GlobalEmbedding.Paper

/-- The actual minimum output norm on the unit sphere, expressed as its real
infimum. For nontrivial finite-dimensional source this infimum is attained, as
proved separately. On a zero source the empty real infimum is zero; the paper's
phase use has tangent dimension at least two and hence nonzero hyperplanes.
Source: `literature/parallelizable-stable-plus-one/main.tex`, `defn:phase`. -/
noncomputable def leastSingularNorm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : E →L[ℝ] F) : ℝ :=
  sInf ((fun z : E ↦ ‖S z‖) '' Metric.sphere (0 : E) 1)

end GlobalEmbedding.Paper
