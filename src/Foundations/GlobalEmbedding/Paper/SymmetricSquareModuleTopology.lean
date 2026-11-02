import GlobalEmbedding.Paper.SymmetricSquare
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Real.Lemmas

namespace GlobalEmbedding.Paper

/-- The canonical real module topology on the existing exact binary symmetric square.
This adds topology only, choosing no norm on the quotient or its original domain.
Source: finite-dimensional symmetric-square bundle in `defn:phase`. -/
abbrev symmetricSquareModuleTopology (V : Type*) [AddCommGroup V] [Module ℝ V] :
    TopologicalSpace (SymmetricSquare V) := moduleTopology ℝ (SymmetricSquare V)

end GlobalEmbedding.Paper
