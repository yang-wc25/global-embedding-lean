import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, chart-independence of the normal second form. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- A maximal-atlas chart sends an interior point to the model interior.
Proof: its smooth local inverse makes its differential surjective, so the existing
Mathlib interior-point theorem applies. Source: `defn:phase`, all smooth charts. -/
theorem general_maximal_chart_range_mem_nhds
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I 2 M) (x : M) (hx : x ∈ e.source) :
    Set.range I ∈ 𝓝 (e.extend I x) := by
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hD : e.MDifferentiable I I := by
    constructor
    · intro z hz
      exact (mdifferentiableAt_of_mem_maximalAtlas he1 hz).mdifferentiableWithinAt
    · intro z hz
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas he1 hz).mdifferentiableWithinAt
  have hi := (hD.mdifferentiableAt hx).isInteriorPoint_of_surjective_mfderiv
    (hD.mfderiv_bijective hx).surjective (BoundarylessManifold.isInteriorPoint (x := x))
  have hm : I (e x) ∈ interior (Set.range I) := by
    simpa only [ModelWithCorners.IsInteriorPoint, mfld_simps] using hi
  exact mem_interior_iff_mem_nhds.mp hm

end GlobalEmbedding.Paper
