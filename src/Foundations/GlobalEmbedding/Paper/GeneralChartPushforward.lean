import GlobalEmbedding.Paper.GeneralChartRangeNeighborhood
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- General-I coordinate pushforward identity, with all chart inverse derivatives justified.
Source: `defn:phase`, local expression of the covariant Hessian. -/
theorem general_chart_pushforward_pointwise
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M) (z : E)
    (hz : z ∈ (extChartAt I x).target)
    (hf : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f
      ((extChartAt I x).symm z))
    (v : TangentSpace I ((extChartAt I x).symm z)) :
    tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f ((extChartAt I x).symm z))
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f ((extChartAt I x).symm z) v) =
    fderiv ℝ (f ∘ (extChartAt I x).symm) z
      (tangentSpaceCastModel 𝓘(ℝ, E) z
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm z) v)) := by
  have hp : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    simpa only [extChartAt_source] using (extChartAt I x).map_target hz
  have hr0 := general_chart_range_mem_nhds (I := I) (chartAt H x)
    (chart_mem_atlas H x) ((extChartAt I x).symm z) hp
  have hr : Set.range I ∈ 𝓝 z := by
    change Set.range I ∈ 𝓝 (extChartAt I x ((extChartAt I x).symm z)) at hr0
    simpa only [(extChartAt I x).right_inv hz] using hr0
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm z :=
    (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt hr
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hz
  rw [mfderivWithin_of_mem_nhds hr] at hi
  have hc := mfderiv_comp z hf hsymm
  rw [mfderiv_eq_fderiv] at hc
  have hv : (mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm z)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm z) v) = v := by
    have h := congrArg (fun L : TangentSpace I ((extChartAt I x).symm z) →L[ℝ]
      TangentSpace I ((extChartAt I x).symm z) ↦ L v) hi
    exact h
  have h := congrArg (fun L ↦ L (mfderiv I 𝓘(ℝ, E)
    (extChartAt I x) ((extChartAt I x).symm z) v)) hc
  have hh := congrArg (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
    (f ((extChartAt I x).symm z))) h.symm
  change tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f ((extChartAt I x).symm z))
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f ((extChartAt I x).symm z)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm z
          (mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm z) v))) =
    fderiv ℝ (f ∘ (extChartAt I x).symm) z
      (tangentSpaceCastModel 𝓘(ℝ, E) z
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm z) v)) at hh
  simpa only [hv] using hh

end GlobalEmbedding.Paper
