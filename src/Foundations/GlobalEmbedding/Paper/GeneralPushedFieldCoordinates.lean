import GlobalEmbedding.Paper.GeneralChartPushforward
import GlobalEmbedding.Paper.GeneralTangentTrivialization
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- Smooth pushed-forward fields agree locally with the differentiated coordinate formula.
Source: `defn:phase`, covariant-Hessian comparison. -/
theorem pushed_tangent_field_general_chart_eventually
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (V : ∀ z : M, TangentSpace I z)
    (x : M) (hf : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 f x) :
    (fun z ↦ tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f ((extChartAt I x).symm z))
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f ((extChartAt I x).symm z)
        (V ((extChartAt I x).symm z)))) =ᶠ[𝓝 (extChartAt I x x)]
    (fun z ↦ fderiv ℝ (f ∘ (extChartAt I x).symm) z
      ((trivializationAt E (TangentSpace I) x
        ⟨(extChartAt I x).symm z, V ((extChartAt I x).symm z)⟩).2)) := by
  have he : ∀ᶠ p in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f p := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf] with p hp
    exact hp.mdifferentiableAt (by norm_num)
  have ht : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    mem_interior_iff_mem_nhds.mp
      ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp
        (BoundarylessManifold.isInteriorPoint (x := x)))
  filter_upwards [ht, extChartAt_preimage_mem_nhds (I := I) (x := x) he] with z hz hF
  rw [tangent_section_general_trivialization_eq_chart_derivative V x _
    (by simpa only [extChartAt_source] using (extChartAt I x).map_target hz)]
  exact general_chart_pushforward_pointwise f x z hz hF (V ((extChartAt I x).symm z))

end GlobalEmbedding.Paper
