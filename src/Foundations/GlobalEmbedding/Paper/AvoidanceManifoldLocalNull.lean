import GlobalEmbedding.Paper.AvoidanceEuclideanLocalNull
import GlobalEmbedding.Paper.AvoidanceManifoldChartRank

/-!
# The actual manifold chart bridge for finite-parameter avoidance

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:avoidance`, lines 940–941.
Use the preferred smooth chart at a relevant point. Its tangent coordinates are those used by
Mathlib's actual manifold derivative, so the equation derivative keeps its rank. An open
Euclidean coordinate neighborhood with null parameter image pulls back to the manifold.
DAG node: `avoidance-manifold-local-projection-null`.
-/

open Manifold MeasureTheory Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- A smooth manifold incidence with actual high-rank derivative has locally null image under a
smooth parameter map. Source: `lem:avoidance`, lines 940–941. The preferred chart identifies the
actual manifold derivative with the ordinary derivative of the coordinate representative.
Apply Euclidean local projected-nullity and pull back its open neighborhood. No Hausdorff,
compactness, connectedness, or second-countability hypothesis is needed for this local step. -/
theorem avoidance_manifold_local_projection_null
    {A M F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [TopologicalSpace M] [ChartedSpace A M] [IsManifold 𝓘(ℝ, A) ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {p : ℕ} {U : Set M} (hU : IsOpen U) {f : M → F}
    (hf : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, F) ∞ f U)
    {α : M → Fin p → ℝ} (hα : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, Fin p → ℝ) ∞ α U)
    {x : M} (hx : x ∈ U) (hzero : f x = 0)
    (hrank : Module.finrank ℝ A < p + Module.finrank ℝ
      (LinearMap.range (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, F) f x).toLinearMap)) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ volume (α '' (V ∩ f ⁻¹' {0})) = 0 := by
  let e := chartAt A x
  let W := e.target ∩ e.symm ⁻¹' U
  let f' := f ∘ e.symm
  let α' := α ∘ e.symm
  have hchart := avoidance_manifold_chart_rank hU hf hx
  change IsOpen W ∧ e x ∈ W ∧ ContDiffOn ℝ ∞ f' W ∧
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f' (e x)).toLinearMap) =
      Module.finrank ℝ (LinearMap.range
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, F) f x).toLinearMap) at hchart
  obtain ⟨hW, hxW, hf', hrankEq⟩ := hchart
  have hxe : x ∈ e.source := mem_chart_source A x
  have hα' : ContDiffOn ℝ ∞ α' W :=
    (avoidance_manifold_chart_rank hU hα hx).2.2.1
  have hfzero : f' (e x) = 0 := by simp only [f', Function.comp_apply, e.left_inv hxe, hzero]
  have hrank' : Module.finrank ℝ A < p + Module.finrank ℝ
      (LinearMap.range (fderiv ℝ f' (e x)).toLinearMap) := by
    rw [hrankEq]
    exact hrank
  obtain ⟨V, hVo, hxV, hVW, hnull⟩ :=
    avoidance_euclidean_local_projection_null hW hf' hα' hxW hfzero hrank'
  refine ⟨e.source ∩ e ⁻¹' V, e.isOpen_inter_preimage hVo, ⟨hxe, hxV⟩, ?_, ?_⟩
  · intro z hz
    have h := (hVW hz.2).2
    change e.symm (e z) ∈ U at h
    simpa only [e.left_inv hz.1] using h
  · apply measure_mono_null _ hnull
    rintro y ⟨z, hz, rfl⟩
    refine ⟨e z, ⟨hz.1.2, ?_⟩, ?_⟩
    · change f (e.symm (e z)) = 0
      simpa only [e.left_inv hz.1.1, Set.mem_preimage, Set.mem_singleton_iff] using hz.2
    · change α (e.symm (e z)) = α z
      rw [e.left_inv hz.1.1]

#print axioms avoidance_manifold_local_projection_null

end GlobalEmbedding.Paper
