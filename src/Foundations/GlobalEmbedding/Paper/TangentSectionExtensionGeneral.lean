import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- Every tangent vector on a smooth manifold with arbitrary model extends to a field C¹
at the point. Proof: use a constant vector in a tangent-bundle trivialization and its
inverse linear trivializations. Source: `defn:phase`, local Hessian comparison. -/
theorem exists_tangent_section_contMDiffAt_general
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (w : TangentSpace I x) :
    ∃ V : ∀ z : M, TangentSpace I z,
      V x = w ∧ ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun z ↦ Bundle.TotalSpace.mk' E z (V z)) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  let c : E := e.continuousLinearMapAt ℝ x w
  let V : ∀ z : M, TangentSpace I z := fun z ↦ e.symmL ℝ z c
  refine ⟨V, ?_, ?_⟩
  · exact e.symmL_continuousLinearMapAt hx w
  · apply (Bundle.contMDiffAt_section (IB := I)
      (n := 1) (F := E) (E := TangentSpace I) x).mpr
    apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with z hz
    change (e ⟨z, e.symmL ℝ z c⟩).2 = c
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hz]
    exact e.continuousLinearMapAt_symmL hz c

end GlobalEmbedding.Paper
