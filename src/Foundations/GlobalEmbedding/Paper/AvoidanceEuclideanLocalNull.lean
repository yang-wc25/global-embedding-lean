import GlobalEmbedding.Paper.RegularLevelLocalGraph
import GlobalEmbedding.Paper.AvoidanceDifferentiableImageNull
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Local nullity from a high-rank Euclidean incidence

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:avoidance`, lines 940–941.
Project the equation onto its actual derivative image to obtain a submersion. Its enlarged zero
set has a regular-level graph of dimension less than the parameter dimension. Any smooth map to
the parameter space therefore sends that local incidence into a Lebesgue-null set.
DAG node: `avoidance-euclidean-local-projection-null`.
-/

open scoped ContDiff
open MeasureTheory Set

namespace GlobalEmbedding.Paper

/-- A smooth incidence whose derivative image has sufficient dimension has locally null image
under any smooth parameter map. Source: `lem:avoidance`, lines 940–941. A projection onto the
actual derivative image makes the equation derivative surjective without decreasing its rank.
The regular-level graph for this projected equation contains the original zero set, and
rank-nullity makes its parameter dimension strictly less than `p`. The lower-dimensional smooth
image theorem and outer-measure monotonicity give the conclusion. -/
theorem avoidance_euclidean_local_projection_null
    {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {p : ℕ} {U : Set A} (hU : IsOpen U) {f : A → F} (hf : ContDiffOn ℝ ∞ f U)
    {α : A → Fin p → ℝ} (hα : ContDiffOn ℝ ∞ α U) {x : A} (hx : x ∈ U)
    (hzero : f x = 0)
    (hrank : Module.finrank ℝ A <
      p + Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)) :
    ∃ V : Set A, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ volume (α '' (V ∩ f ⁻¹' {0})) = 0 := by
  classical
  let L := fderiv ℝ f x
  let R := L.range
  obtain ⟨Q, hQ⟩ := R.exists_isCompl
  let π : F →L[ℝ] R := (R.projectionOnto Q hQ).toContinuousLinearMap
  let q : A → R := π ∘ f
  have hd : HasFDerivAt f L x :=
    ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdq : fderiv ℝ q x = π.comp L := (π.hasFDerivAt.comp x hd).fderiv
  have hsurj : Function.Surjective (fderiv ℝ q x) := by
    rw [hdq]
    intro v
    obtain ⟨u, hu⟩ := v.property
    refine ⟨u, ?_⟩
    change π (L u) = v
    change L u = (v : F) at hu
    rw [hu]
    exact R.projectionOnto_apply_left hQ v
  have hq : ContDiffOn ℝ ∞ q U := π.contDiff.comp_contDiffOn hf
  have hqzero : q x = 0 := by simp [q, hzero]
  obtain ⟨hdim, V, W, g, hVo, hxV, hVU, hWo, h0W, hg, him⟩ :=
    regular_level_local_graph hU hq hx hqzero hsurj
  have hK : Module.finrank ℝ (fderiv ℝ q x).ker < p := by
    change Module.finrank ℝ A < p + Module.finrank ℝ R at hrank
    omega
  have hmaps : MapsTo g W U := by
    intro z hz
    exact hVU ((him ▸ mem_image_of_mem g hz).1)
  have hcomp : DifferentiableOn ℝ (α ∘ g) W :=
    (hα.comp hg hmaps).differentiableOn (by simp)
  have hn := avoidance_differentiable_image_null hK W (α ∘ g) hcomp
  refine ⟨V, hVo, hxV, hVU, measure_mono_null ?_ hn⟩
  rintro y ⟨z, hz, rfl⟩
  have hzq : z ∈ V ∩ q ⁻¹' {0} := by
    refine ⟨hz.1, ?_⟩
    change π (f z) = 0
    rw [hz.2]
    exact map_zero π
  rw [← him] at hzq
  obtain ⟨w, hw, rfl⟩ := hzq
  exact ⟨w, hw, rfl⟩

#print axioms avoidance_euclidean_local_projection_null

end GlobalEmbedding.Paper
