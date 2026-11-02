import Repair.AuxBridgeNovOpenMetricNormTransport
import Probes.Round3ParameterJointConclusion

/-! The internal Fopen conclusion transports to the unchanged original Data.F
for the SAME actual U.  Its actual tensor germ is restricted to the original
open parameter region and transported there.  The map germs, smoothness and
map estimates already concern the same U and are retained literally.  This
adds no output regularity hypothesis beyond the internal proved conclusion. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem auxBridgeNov_open_metric_error_germ
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (U : P × M → Ey) (delta : ℝ)
    (G : Set (P × M)) (hG : G ⊆ incrementsOriginalParameterRegion Data)
    (hInternal : incrementsOriginalMetricError
      (fun z => fullIncrementNovOriginalSourceSlice Data z.1 z.2) U Data.H delta ∈
      parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) G) :
    incrementsOriginalMetricError Data.F U Data.H delta ∈
      parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) G := by
  constructor
  · intro i
    obtain ⟨V,hV,hSV,hSmooth⟩ := hInternal.1 i
    let O := incrementsOriginalDifferentiation Data.atlas Data.parameterChart i
    let W := O ∩ (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹'
      incrementsOriginalParameterRegion Data
    have hO : IsOpen O :=
      parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i
    have hW : IsOpen W :=
      (parameterRound2_originalJointPoint_continuousOn Data.atlas Data.parameterChart i).isOpen_inter_preimage
        hO (hd.parameter_open.prod isOpen_univ)
    have hSW : incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i ⊆ W := by
      intro y hy
      exact ⟨hy.1,hd.parameter_subset hy.2.2.2,mem_univ _⟩
    refine ⟨V ∩ W,hV.inter hW,fun y hy => ⟨hSV hy,hSW hy⟩,?_⟩
    apply (hSmooth.mono inter_subset_left).congr
    intro y hy
    funext k
    unfold incrementsOriginalTensorCoordinates
    rw [fullIncrementNov_original_metric_error_eq_open_source Data U delta _ hy.2.2.1]
  · intro z hz
    rw [fullIncrementNov_original_metric_error_eq_open_source Data U delta z.1 (hG hz).1 z.2]
    exact hInternal.2 z hz

/-- Every field of the actual internal all-order conclusion now refers to
Data.F and the SAME U, original norm domains and target tensor. -/
theorem auxBridgeNov_open_joint_increment_conclusion
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (U : P × M → Ey)
    (G : Set (P × M)) (hG : G ⊆ incrementsOriginalParameterRegion Data)
    (q : ℕ) (delta tau ell : ℝ) (Cmap Cmetric : ℕ → ℝ)
    (hInternal : Round3ParameterJointIncrementConclusion Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) G
      (fun z => fullIncrementNovOriginalSourceSlice Data z.1 z.2) U Data.H q delta tau ell Cmap Cmetric) :
    Round3ParameterJointIncrementConclusion Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) G Data.F U Data.H q delta tau ell Cmap Cmetric := {
  joint_smooth := hInternal.joint_smooth
  map_germs := hInternal.map_germs
  metric_germ := auxBridgeNov_open_metric_error_germ Data hd U delta G hG hInternal.metric_germ
  map0 := hInternal.map0
  map1 := hInternal.map1
  metric := by
    intro j
    have h := hInternal.metric j
    rwa [auxBridgeNov_open_metric_error_weighted_eq Data hd U delta 0 j tau] at h }

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.auxBridgeNov_open_metric_error_germ
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_open_joint_increment_conclusion
