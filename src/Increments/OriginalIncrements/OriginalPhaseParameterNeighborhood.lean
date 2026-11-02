import OriginalIncrements.FiniteJetNeighborhood
import OriginalIncrements.OriginalPhysicalPhaseJets

/-!
# Original finite phase jets control one actual parameter neighborhood

The original `Given` entries at orders zero and one are evaluated only on
the original compact parameter set and the unchanged owner sampling domains.
Their continuity extends those two bounds, with slack one, to a single open
parameter neighborhood on every active original raw parent. The raw parent
supports and original relative cutoff support supply the active carriers;
no estimate outside the original parameter set is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

variable [CompactSpace M]

/-- Only the original finite two-entry budget is an input. The resulting
neighborhood is chosen once for all owner labels and phases, before every
later high derivative order and before the parameter localization. -/
theorem original_phase_low_jets_parameter_neighborhood
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hFinite : ∀ k ≤ 1, actualOriginalGivenInputProfile Data k ell ≠ ⊤)
    (hBudget : ∀ k ≤ 1, (actualOriginalGivenInputProfile Data k ell).toReal ≤ Packet k) :
    let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ V : Set P, IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      ∀ (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
        (k : ℕ), k ≤ 1 → ∀ z : P × M, z.1 ∈ V →
        z ∈ tsupport (theta i) → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
        originalPhaseJetAtPhysical Data nu i k ell z <
          actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1 := by
  intro theta
  let I := Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) × Fin 2
  let active : I → Set (P × M) := fun a => tsupport (theta a.2.1) ∩ tsupport (Data.cutoff a.1)
  let domain : I → Set (P × M) := fun a => originalPhasePhysicalDomain Data a.1 a.2.1
  let f : I → P × M → ℝ := fun a => originalPhaseJetAtPhysical Data a.1 a.2.1 a.2.2 ell
  let bound : I → ℝ := fun a => actualOriginalTotalPhaseJetCost (m+1) d a.2.2*Packet a.2.2
  have hRelative (nu : Fin Data.primaryCount) :
      incrementsOriginalRelativeCutoffSupport Data nu =
        incrementsOriginalParameterRegion Data ∩ tsupport (Data.cutoff nu) :=
    original_relative_cutoff_support_eq Data hd nu
  have hParent (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : P × M)
      (hz : z ∈ tsupport (theta i)) :=
    original_raw_parent_own_samples Data B hChart BS TS BP TP Ds Dp RS RP hSource hParameter i z hz
  have hAD (a : I) :
      (Data.parameterOpen ×ˢ (univ : Set M)) ∩ active a ⊆ domain a := by
    intro z hz
    have hp := hParent a.2.1 z hz.2.1
    exact ⟨⟨hp.1,hp.2.1⟩,hd.cutoff_support_local a.1 ((hRelative a.1).symm ▸ ⟨hz.1,hz.2.2⟩),hz.1⟩
  have hD (a : I) : IsOpen (domain a) := original_phase_physical_domain_isOpen Data hd a.1 a.2.1
  have hCont (a : I) : ContinuousOn (f a) (domain a) :=
    original_phase_jet_physical_continuousOn Data hd hs a.1 a.2.1 a.2.2 ell
  have hBound (a : I) (z : P × M)
      (hz : z ∈ (Data.parameterSet ×ˢ (univ : Set M)) ∩ active a) : f a z ≤ bound a := by
    have hp := hParent a.2.1 z hz.2.1
    have hPrimary : z ∈ Data.primaryDomain a.1 := hd.cutoff_support_local a.1
      ((hRelative a.1).symm ▸ ⟨⟨hd.parameter_subset hz.1.1,hz.1.2⟩,hz.2.2⟩)
    exact original_phase_jet_physical_original_sample_bound Data hd hs a.1 a.2.1 a.2.2
      ell (Packet a.2.2) hell (hFinite a.2.2 (by omega)) (hBudget a.2.2 (by omega)) z
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hz.1.1 hPrimary
  obtain ⟨V,hV,hKV,hVU,hVbound⟩ := finite_active_inputs_parameter_neighborhood
    Data.parameterSet Data.parameterOpen hd.parameter_open hd.parameter_subset active domain
    (fun _ => (isClosed_tsupport _).inter (isClosed_tsupport _)) hD hAD f bound hCont hBound 1 zero_lt_one
  refine ⟨V,hV,hKV,hVU,?_⟩
  intro nu i k hk z hz htheta hcutoff
  have h := hVbound (nu,i,⟨k,by omega⟩) z
    ⟨⟨hz,mem_univ _⟩,htheta,((hRelative nu) ▸ hcutoff).2⟩
  exact h

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_phase_low_jets_parameter_neighborhood
