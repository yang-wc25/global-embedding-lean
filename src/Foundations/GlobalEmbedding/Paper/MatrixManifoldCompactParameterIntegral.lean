import GlobalEmbedding.Paper.MatrixSmoothCompactParameterIntegral
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Smooth compact-period integrals on manifolds

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
lines 307–315. DAG node: `matrix-manifold-compact-parameter-integral`.
-/

open Set MeasureTheory
open scoped Manifold ContDiff Topology

universe u v w

namespace GlobalEmbedding.Paper

/-- Integration over a compact period preserves native manifold `C^n` regularity, for every
finite order and true infinity, on any finite-dimensional manifold without boundary.

Proof: use any actual source chart. Compose its smooth inverse times the time identity
with the original jointly smooth integrand. The native normed compact-parameter integral
is smooth on the open chart target. Compose this local smooth integral with the smooth
chart. The actual chart inverse identity identifies it with the original integral on the
chart source neighborhood, so eventual equality gives native smoothness at the base point.
Source: `prop:matrix` proof, lines 307–315. -/
theorem contMDiff_compact_parameter_integral
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Q : Type v} [TopologicalSpace Q] [ChartedSpace P Q]
    {E : Type (max u w)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ∞) [IsManifold 𝓘(ℝ, P) n Q]
    (F : Q × ℝ → E)
    (hF : ContMDiff ((𝓘(ℝ, P)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n F) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) n
      (fun q ↦ ∫ t in Icc (0 : ℝ) 1, F (q, t)) := by
  intro q
  let e := chartAt P q
  have hinv : ContMDiffOn 𝓘(ℝ, P) 𝓘(ℝ, P) n e.symm e.target :=
    contMDiffOn_chart_symm
  have hpair : ContMDiffOn 𝓘(ℝ, P × ℝ) ((𝓘(ℝ, P)).prod 𝓘(ℝ, ℝ)) n
      (fun z : P × ℝ ↦ (e.symm z.1, z.2)) (e.target ×ˢ univ) := by
    have hfst : ContMDiffOn 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P) n
        (Prod.fst : P × ℝ → P) (e.target ×ˢ univ) :=
      contDiff_fst.contMDiff.contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, P × ℝ) 𝓘(ℝ, ℝ) n
        (Prod.snd : P × ℝ → ℝ) (e.target ×ˢ univ) :=
      contDiff_snd.contMDiff.contMDiffOn
    exact (hinv.comp hfst (fun z hz ↦ hz.1)).prodMk hsnd
  have hchart : ContDiffOn ℝ n
      (fun z : P × ℝ ↦ F (e.symm z.1, z.2)) (e.target ×ˢ univ) :=
    (hF.comp_contMDiffOn hpair).contDiffOn
  have hIc : ContDiffOn ℝ n
      (fun y : P ↦ ∫ t in Icc (0 : ℝ) 1, F (e.symm y, t)) e.target :=
    contDiffOn_compact_parameter_integral n e.target e.open_target _ hchart
  have hq : q ∈ e.source := mem_chart_source P q
  have htarget : e q ∈ e.target := e.map_source hq
  have hIcAt : ContDiffAt ℝ n
      (fun y : P ↦ ∫ t in Icc (0 : ℝ) 1, F (e.symm y, t)) (e q) :=
    hIc.contDiffAt (e.open_target.mem_nhds htarget)
  have heAt : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, P) n e q :=
    (contMDiffOn_chart (I := 𝓘(ℝ, P))).contMDiffAt (e.open_source.mem_nhds hq)
  have hcomp := hIcAt.contMDiffAt.comp q heAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hq] with z hz
  simp only [Function.comp_apply, e.left_inv hz]

#print axioms contMDiff_compact_parameter_integral

end GlobalEmbedding.Paper
