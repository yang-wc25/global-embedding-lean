import GlobalEmbedding.Paper.GeneralChartContDiff
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- C¹ tangent fields have differentiable coordinate components in a general extended
chart on the actual boundaryless manifold. Source: `defn:phase`, covariant Hessians. -/
theorem tangent_section_general_chart_coordinates_differentiable
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] (V : ∀ z : M, TangentSpace I z) (x : M)
    (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ Bundle.TotalSpace.mk' E z (V z)) x) :
    DifferentiableAt ℝ (fun z ↦ (trivializationAt E (TangentSpace I) x
      ⟨(extChartAt I x).symm z, V ((extChartAt I x).symm z)⟩).2) (extChartAt I x x) := by
  have hc := (Bundle.contMDiffAt_section (IB := I)
    (n := 1) (F := E) (E := TangentSpace I) x).mp hV
  exact (contDiffAt_general_chart_representative hc).differentiableAt (by norm_num)

end GlobalEmbedding.Paper
