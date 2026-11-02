import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Count

/-!
# Nullity from local projected-nullity neighborhoods

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:avoidance`, lines 940–941.
Second countability supplies a countable subcover of the arbitrary relevant incidence set.
DAG node: `avoidance-countable-local-null`.
-/

open MeasureTheory Set

namespace GlobalEmbedding.Paper

/-- Local nullity of the image of an arbitrary set implies global nullity in a second-countable
source. Source: `lem:avoidance`, lines 940–941. Select a countable open subcover of the relevant
set and contain its image in the corresponding countable union of null images. Neither the
set nor its image must be measurable, and the image map need not be continuous. -/
theorem avoidance_image_null_of_locally_null
    {X Z : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace Z]
    (μ : Measure Z) (R : Set X) (f : X → Z)
    (hlocal : ∀ x ∈ R, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ (f '' (R ∩ U)) = 0) :
    μ (f '' R) = 0 := by
  classical
  choose U hU hxU hnull using fun x : R ↦ hlocal x x.property
  have hcover : R ⊆ ⋃ i : R, U i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨t, ht, htcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover U hU hcover
  have hsub : f '' R ⊆ ⋃ i ∈ t, f '' (R ∩ U i) := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp (htcov hx)
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hit, ⟨x, ⟨hx, hxi⟩, rfl⟩⟩⟩
  apply measure_mono_null hsub
  exact (measure_biUnion_null_iff ht).mpr fun i hi ↦ hnull i

#print axioms avoidance_image_null_of_locally_null

end GlobalEmbedding.Paper
