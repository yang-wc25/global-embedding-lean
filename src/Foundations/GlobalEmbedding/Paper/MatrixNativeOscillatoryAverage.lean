import GlobalEmbedding.Paper.MatrixCompactUniformOscillatoryCosAverage
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Actual nonlinear oscillatory decay on compact native manifolds

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:matrix, line293.
DAG: `matrix-native-uniform-oscillatory-average`.
The existing genuine normed cutoff/integration-by-parts theorem is transported
through actual charts. No critical-set estimate or uniform decay is assumed.
-/

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Actual smooth periodic scalar families on a compact native manifold have uniform
oscillatory cosine decay when each actual phase profile is analytic and nonconstant.

Proof: inside an actual source chart choose a compact coordinate neighborhood contained
in its open target. The actual inverse-chart pullbacks satisfy the accepted normed
oscillatory theorem. The inverse identity transfers its uniform estimate to a neighborhood
of the source point. Thus convergence is locally uniform; actual source compactness makes
it uniform. Source: prop:matrix, compact uniform oscillatory argument, line293. -/
theorem native_uniform_oscillatory_cos_average
    {P M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(ℝ, P) ∞ M]
    [CompactSpace M] (φ a : M × ℝ → ℝ)
    (hφ : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (ha : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ a)
    (hφperiod : ∀ p, Function.Periodic (fun t ↦ φ (p, t)) 1)
    (haperiod : ∀ p, Function.Periodic (fun t ↦ a (p, t)) 1)
    (hanalytic : ∀ p, AnalyticOnNhd ℝ (fun t ↦ φ (p, t)) univ)
    (hnonconstant : ∀ p, ∃ x y : ℝ, φ (p, x) ≠ φ (p, y)) (phase : ℝ) :
    TendstoUniformly
      (fun T : ℝ ↦ fun p : M ↦ ∫ t in Icc (0 : ℝ) 1,
        a (p, t) * Real.cos (T * φ (p, t) + phase))
      (fun _ : M ↦ (0 : ℝ)) atTop := by
  apply tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
  intro V hV q
  let e := chartAt P q
  have hq : q ∈ e.source := mem_chart_source P q
  obtain ⟨K, hK, hKi, hKt⟩ := exists_compact_subset e.open_target (e.map_source hq)
  have hinv : ContMDiffOn 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ e.symm e.target :=
    contMDiffOn_chart_symm
  have hpair : ContMDiffOn 𝓘(ℝ, P × ℝ) (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : P × ℝ ↦ (e.symm z.1, z.2)) (e.target ×ˢ univ) := by
    have hfst : ContMDiffOn 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P) ∞
        (Prod.fst : P × ℝ → P) (e.target ×ˢ univ) :=
      contDiff_fst.contMDiff.contMDiffOn
    exact (hinv.comp hfst (fun z hz ↦ hz.1)).prodMk
      contDiff_snd.contMDiff.contMDiffOn
  have hc := compact_uniform_oscillatory_cos_average e.open_target hK hKt
    (fun z : P × ℝ ↦ φ (e.symm z.1, z.2))
    (fun z : P × ℝ ↦ a (e.symm z.1, z.2))
    (hφ.comp_contMDiffOn hpair).contDiffOn (ha.comp_contMDiffOn hpair).contDiffOn
    (fun p _ ↦ hφperiod (e.symm p)) (fun p _ ↦ haperiod (e.symm p))
    (fun p _ ↦ hanalytic (e.symm p)) (fun p _ ↦ hnonconstant (e.symm p)) phase
  have he : ContinuousAt e q := e.continuousAt hq
  refine ⟨e.source ∩ e ⁻¹' K,
    inter_mem (e.open_source.mem_nhds hq)
      (he.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hKi)), ?_⟩
  filter_upwards [hc V hV] with T hT p hp
  have h := hT (e p) hp.2
  simpa only [e.left_inv hp.1] using h

#print axioms native_uniform_oscillatory_cos_average

end GlobalEmbedding.Paper
