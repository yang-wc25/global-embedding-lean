import GlobalEmbedding.Paper.NativeChartGluing
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Reuse native chart gluing on the actual open parameter domain

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines417–418.
DAG node: `balanced-native-chart-gluing-on-open`.
-/

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Compatible native-smooth local chart values on an actual open source subset
produce an actual total function smooth on that same subset, with no regularity
or compatibility requirement outside it.

Proof: if the actual open subset is empty, use zero. Otherwise restrict the actual
chart maps to its actual native open submanifold and apply the existing accepted
native_chart_gluing theorem verbatim. Extend that actual glued function by zero
as a total function. The native open-submanifold smoothness equivalence gives
ContMDiffOn on the original open set. Exact actual local values are retained.
This is the parameter-domain bridge for the source's single interval; it does
not assume a globally smooth parameter family. Source: `lem:balanced`, lines417–418. -/
theorem balanced_native_chart_gluing_on_open
    {E F H K M N V ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K) (n : ℕ∞ω)
    (S : Set M) (hS : IsOpen S)
    (e : ι → OpenPartialHomeomorph M N) (localValue : ι → N → V)
    (hcover : ∀ x ∈ S, ∃ i : ι, x ∈ (e i).source)
    (he : ∀ i, ContMDiffOn I J n (e i) (e i).source)
    (hlocal : ∀ i, ContMDiffOn J 𝓘(ℝ, V) n (localValue i) (e i).target)
    (hcompat : ∀ (i j : ι) (x : M), x ∈ S →
      x ∈ (e i).source → x ∈ (e j).source →
      localValue i (e i x) = localValue j (e j x)) :
    ∃ value : M → V, ContMDiffOn I 𝓘(ℝ, V) n value S ∧
      ∀ (i : ι) (x : M), x ∈ S → x ∈ (e i).source →
        value x = localValue i (e i x) := by
  classical
  let O : Opens M := ⟨S, hS⟩
  by_cases hne : Nonempty O
  · let er : ι → OpenPartialHomeomorph O N := fun i ↦ (e i).subtypeRestr hne
    have hcoverO (x : O) : ∃ i : ι, x ∈ (er i).source := by
      obtain ⟨i, hi⟩ := hcover x.val x.property
      exact ⟨i, by simpa only [er, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hi⟩
    have her (i : ι) : ContMDiffOn I J n (er i) (er i).source := by
      have hval : ContMDiff I I n (Subtype.val : O → M) := contMDiff_subtype_val
      change ContMDiffOn I J n (fun x : O ↦ e i x.val) (er i).source
      exact (he i).comp hval.contMDiffOn
        (fun x hx ↦ by simpa only [er, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx)
    have hlocalr (i : ι) : ContMDiffOn J 𝓘(ℝ, V) n (localValue i) (er i).target :=
      (hlocal i).mono ((e i).subtypeRestr_target_subset hne)
    have hcompatr (i j : ι) (x : O) (hxi : x ∈ (er i).source)
        (hxj : x ∈ (er j).source) :
        localValue i (er i x) = localValue j (er j x) :=
      hcompat i j x.val x.property
        (by simpa only [er, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxi)
        (by simpa only [er, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxj)
    obtain ⟨v, hv, heq⟩ := native_chart_gluing I J n er localValue hcoverO her hlocalr hcompatr
    let value : M → V := fun x ↦ if hx : x ∈ S then v ⟨x, hx⟩ else 0
    have hrestrict : (fun x : O ↦ value x.val) = v := by
      funext x
      have hx : x.val ∈ S := x.property
      simp only [value, dite_eq_left hx]
    refine ⟨value, ?_, ?_⟩
    · intro x hx
      have hvAt : ContMDiffAt I 𝓘(ℝ, V) n (fun y : O ↦ value y.val) ⟨x, hx⟩ := by
        rw [hrestrict]
        exact hv.contMDiffAt
      exact (contMDiffAt_subtype_iff.mp hvAt).contMDiffWithinAt
    · intro i x hx hxi
      change (if hy : x ∈ S then v ⟨x, hy⟩ else 0) = localValue i (e i x)
      rw [dite_eq_left hx]
      apply heq i ⟨x, hx⟩
      simpa only [er, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxi
  · have hsempty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hne ⟨⟨x, hx⟩⟩
    subst S
    exact ⟨fun _ ↦ 0, contMDiffOn_const, by simp⟩

#print axioms balanced_native_chart_gluing_on_open

end GlobalEmbedding.Paper
