import Upgrade.ProbeInterface
import GlobalEmbedding.Paper.AvoidanceCountableLocalNull
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Pull actual two-chart incidence nullity back to the source pair space

The source points may lie in different charts or different components.
The parameter is unchanged by the product chart. Consequently a null image
proved for the literal coordinate incidence pulls back to the actual source
incidence without any Jacobian or source measure. Global nullity then uses
the already accepted countable-local-null theorem.
-/

noncomputable section
open Function Set MeasureTheory

namespace GlobalEmbedding.Upgrade
open Paper

variable {P M E Z : Type*}
  [TopologicalSpace P] [TopologicalSpace M] [PseudoMetricSpace E]
  [MeasurableSpace Z]

/-- Product of the unchanged parameter coordinate and two independently
chosen actual source charts. -/
def actualPairChart (A : BufferedAtlas M E) (i j : Fin A.count) :
    OpenPartialHomeomorph (P × (M × M)) (P × (E × E)) :=
  (OpenPartialHomeomorph.refl P).prod ((A.chart i).prod (A.chart j))

/-- An actual coordinate-incidence null image pulls back with exactly the
same parameter projection. No connectedness, orientation or source measure
is involved. `R` is the actual relevant incidence set chosen by the caller. -/
theorem actual_pair_chart_pullback_null
    (A : BufferedAtlas M E) (i j : Fin A.count) (μ : Measure Z) (α : P → Z)
    (R : Set (P × (M × M))) (w : P × (M × M))
    (hx : w.2.1 ∈ (A.chart i).source) (hy : w.2.2 ∈ (A.chart j).source)
    (W : Set (P × (E × E))) (hW : IsOpen W)
    (hw : actualPairChart A i j w ∈ W)
    (hnull : μ ((fun z : P × (E × E) ↦ α z.1) ''
      (W ∩ (actualPairChart A i j).symm ⁻¹' R)) = 0) :
    ∃ U : Set (P × (M × M)), IsOpen U ∧ w ∈ U ∧
      μ ((fun z : P × (M × M) ↦ α z.1) '' (R ∩ U)) = 0 := by
  let e := actualPairChart (P := P) A i j
  have hwe : w ∈ e.source := by
    exact ⟨mem_univ _, hx, hy⟩
  refine ⟨e.source ∩ e ⁻¹' W, e.isOpen_inter_preimage hW, ⟨hwe, hw⟩, ?_⟩
  apply measure_mono_null ?_ hnull
  rintro q ⟨z, hz, rfl⟩
  refine ⟨e z, ⟨hz.2.2, ?_⟩, ?_⟩
  · change e.symm (e z) ∈ R
    rw [e.left_inv hz.2.1]
    exact hz.1
  · rfl

/-- Apply the accepted local-to-global null-image theorem after the actual
pair-chart pullback. This is a coordinate dictionary, not a new proof of
finite-parameter avoidance or an assumed good perturbation. -/
theorem actual_pair_incidence_parameter_image_null [SecondCountableTopology (P × (M × M))]
    (A : BufferedAtlas M E) (μ : Measure Z) (α : P → Z)
    (R : Set (P × (M × M)))
    (hlocal : ∀ w ∈ R, ∃ (i j : Fin A.count) (W : Set (P × (E × E))),
      w.2.1 ∈ (A.chart i).source ∧ w.2.2 ∈ (A.chart j).source ∧
      IsOpen W ∧ actualPairChart A i j w ∈ W ∧
      μ ((fun z : P × (E × E) ↦ α z.1) ''
        (W ∩ (actualPairChart A i j).symm ⁻¹' R)) = 0) :
    μ ((fun z : P × (M × M) ↦ α z.1) '' R) = 0 := by
  apply avoidance_image_null_of_locally_null μ R (fun z ↦ α z.1)
  intro w hw
  obtain ⟨i, j, W, hx, hy, hW, hwW, hnull⟩ := hlocal w hw
  exact actual_pair_chart_pullback_null A i j μ α R w hx hy W hW hwW hnull

#print axioms actual_pair_chart_pullback_null
#print axioms actual_pair_incidence_parameter_image_null

end GlobalEmbedding.Upgrade
