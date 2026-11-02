import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Actual global native-smooth functions from compatible actual local chart values

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-native-chart-gluing`.
-/

open Set
open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Compatible actual native-C^n local values on an actual open chart cover glue to an actual
native-C^n global function, agreeing exactly with every local expression.

For each point choose an actual covering chart and use its actual local value. Compatibility
identifies this value with every other chart expression at that point. Near each point the
global function therefore equals one fixed local composite. The genuine local value and
chart smoothness on their actual open target/source prove native smoothness of that composite
and hence of the actual global function. No global function existence or continuity is
assumed. Source: gluing by overlap uniqueness at the end of the proof of `lem:balanced`. -/
theorem native_chart_gluing
    {E F H K M N V ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K) (n : ℕ∞ω)
    (e : ι → OpenPartialHomeomorph M N) (localValue : ι → N → V)
    (hcover : ∀ x : M, ∃ i : ι, x ∈ (e i).source)
    (he : ∀ i, ContMDiffOn I J n (e i) (e i).source)
    (hlocal : ∀ i, ContMDiffOn J (𝓘(ℝ, V)) n (localValue i) (e i).target)
    (hcompat : ∀ (i j : ι) (x : M), x ∈ (e i).source → x ∈ (e j).source →
      localValue i (e i x) = localValue j (e j x)) :
    ∃ value : M → V, ContMDiff I (𝓘(ℝ, V)) n value ∧
      ∀ (i : ι) (x : M), x ∈ (e i).source → value x = localValue i (e i x) := by
  classical
  let index : M → ι := fun x ↦ (hcover x).choose
  let value : M → V := fun x ↦ localValue (index x) (e (index x) x)
  have heq (i : ι) (x : M) (hx : x ∈ (e i).source) : value x = localValue i (e i x) :=
    hcompat (index x) i x (hcover x).choose_spec hx
  refine ⟨value, ?_, heq⟩
  intro x
  let i := index x
  have hx : x ∈ (e i).source := (hcover x).choose_spec
  have hf := (hlocal i).contMDiffAt
    ((e i).open_target.mem_nhds ((e i).map_source hx))
  have hc := (he i).contMDiffAt ((e i).open_source.mem_nhds hx)
  apply (hf.comp x hc).congr_of_eventuallyEq
  filter_upwards [(e i).open_source.mem_nhds hx] with y hy
  exact heq i y hy

#print axioms native_chart_gluing

end GlobalEmbedding.Paper
