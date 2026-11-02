import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-! Actual chart-linear phase in the local realization step of original
thm:upgrade1053–1057. DAG: upgrade-local-linear-phase. No new tangent norm. -/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Every actual cotangent at x is realized by an actual smooth chart-linear
phase. On the original chart source its differential is the original covector
composed with the actual chart differential, so the coordinate kernel is fixed.

Proof: take psi=xi composed with extChartAt I x. Native smoothness of the chart
and the supplied CLM gives local smoothness. The actual chain rule and native
CLM differential compute dpsi. At x the native actual chart differential is the
identity, giving precisely xi. No phase, normal frame, metric, or desired
extension is supplied. Source: original main.tex1053–1057. -/
theorem upgrade_exists_local_linear_phase
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M]
    (x : M) (xi : TangentSpace I x →L[ℝ] ℝ) :
    ∃ psi : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ psi (chartAt H x).source ∧
      (∀ z ∈ (chartAt H x).source,
        mfderiv I 𝓘(ℝ, ℝ) psi z = xi.comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x) z)) ∧
      mfderiv I 𝓘(ℝ, ℝ) psi x = xi := by
  let eta : E →L[ℝ] ℝ := xi
  let psi : M → ℝ := eta ∘ extChartAt I x
  have hs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ psi (chartAt H x).source :=
    eta.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt (I := I) (x := x))
  have hd (z : M) (hz : z ∈ (chartAt H x).source) :
      mfderiv I 𝓘(ℝ, ℝ) psi z = eta.comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x) z) := by
    change mfderiv I 𝓘(ℝ, ℝ) (eta ∘ extChartAt I x) z = _
    rw [mfderiv_comp z eta.differentiableAt.mdifferentiableAt (mdifferentiableAt_extChartAt hz)]
    rw [mfderiv_eq_fderiv, eta.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  refine ⟨psi, hs, hd, ?_⟩
  rw [hd x (mem_chart_source H x), mfderiv_extChartAt_self]
  apply ContinuousLinearMap.ext
  intro v
  rfl

#print axioms upgrade_exists_local_linear_phase

end GlobalEmbedding.Paper
