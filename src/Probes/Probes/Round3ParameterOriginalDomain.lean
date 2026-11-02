import Probes.Round3ParameterWholeDomainRegularity
import GlobalEmbedding.Paper.IncrementsOriginalQualitativeAdmissibility

/-! One canonical physical parameter domain from the ORIGINAL parameter
atlas.  It contains all K×M and every original evaluation sample.  For the
original compact-parameter repair caller K=P, it is literally all P×M.
No chartwise increment or stagewise intersection is used. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin n)

def round3ParameterOriginalDomain (Data : IncrementsOriginalNativeData n d N M P) : Set (P × M) :=
  {z | z.1 ∈ Data.parameterOpen ∧ ∃ b, z.1 ∈ (Data.parameterChart b).source}

theorem round3ParameterOriginalDomain_open (Data : IncrementsOriginalNativeData n d N M P)
    (hO : IsOpen Data.parameterOpen) : IsOpen (round3ParameterOriginalDomain Data) := by
  have hcharts : IsOpen (⋃ b, (Data.parameterChart b).source) := isOpen_iUnion (fun b => (Data.parameterChart b).open_source)
  have he : round3ParameterOriginalDomain Data =
      (Prod.fst : P × M → P) ⁻¹' (Data.parameterOpen ∩ ⋃ b, (Data.parameterChart b).source) := by
    ext z
    simp only [round3ParameterOriginalDomain,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_inter_iff,Set.mem_iUnion]
  rw [he]
  exact (hO.inter hcharts).preimage continuous_fst

theorem round3ParameterOriginalDomain_cover (Data : IncrementsOriginalNativeData n d N M P) :
    ∀ z ∈ round3ParameterOriginalDomain Data, ∃ b, z.1 ∈ (Data.parameterChart b).source :=
  fun _ hz => hz.2

theorem round3ParameterOriginalDomain_subset (Data : IncrementsOriginalNativeData n d N M P) :
    round3ParameterOriginalDomain Data ⊆ incrementsOriginalParameterRegion Data :=
  fun _ hz => ⟨hz.1,Set.mem_univ _⟩

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem round3ParameterOriginalDomain_contains_parameters
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data) :
    Data.parameterSet ×ˢ (Set.univ : Set M) ⊆ round3ParameterOriginalDomain Data := by
  intro z hz
  obtain ⟨b,hb,_⟩ := hd.parameter_cover z.1 hz.1
  exact ⟨hd.parameter_subset hz.1,b,hb⟩

theorem round3ParameterOriginalDomain_contains_samples
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data) :
    ∀ i, MapsTo (incrementsOriginalJointPoint Data.atlas Data.parameterChart i)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) (round3ParameterOriginalDomain Data) := by
  intro i y hy
  exact round3ParameterOriginalDomain_contains_parameters Data hd ⟨hy.2.2.2,Set.mem_univ _⟩

theorem round3ParameterOriginalDomain_eq_univ
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hK : Data.parameterSet = univ) : round3ParameterOriginalDomain Data = univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact round3ParameterOriginalDomain_contains_parameters Data hd ⟨by rw [hK]; trivial,Set.mem_univ _⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterOriginalDomain_eq_univ
