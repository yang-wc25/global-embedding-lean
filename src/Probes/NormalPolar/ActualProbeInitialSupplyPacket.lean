import NormalPolar.ActualProbeInitialSupplyReferenceTarget

/-! The exact immutable repair packet as the initial raw producer's atlas.
The existing parameter charts, inner sets, buffer and samples are retained.
Their global cover follows from the actual original partition preparation.
The normalization lemma only connects the internally produced physical error
to the packet's literal normalized defect, without changing the first map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IM) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference Given : ℕ → ℝ}

def actualProbeInitialParameterAtlas
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hK : Data.parameterSet = univ) : BufferedAtlas P Ep where
  count := Data.parameterCount
  chart := packet.parameterFamily.chart
  inner := packet.parameterFamily.inner
  inner_open := packet.parameterFamily.inner_open
  inner_subset := packet.parameterFamily.inner_subset
  cover := by
    intro p
    obtain ⟨i,hi⟩ := packet.parameterPreparation.plateau_on p (by rw [hK]; exact mem_univ _)
    refine ⟨i,packet.parameterPreparation.inner_support i (subset_tsupport _ ?_)⟩
    rw [Function.mem_support,hi]
    exact one_ne_zero
  buffer := packet.parameterFamily.buffer
  buffer_pos := packet.parameterFamily.buffer_pos
  buffered := packet.parameterFamily.buffered
  support := packet.parameterFamily.inner

theorem actualProbeInitialSupply_parameter_atlas_smooth
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hK : Data.parameterSet = univ) : IsSmoothBufferedAtlas (actualProbeInitialParameterAtlas packet hK) := by
  constructor
  · intro i
    change packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth i
  · exact packet.parameterFamily.inner_subset

theorem actualProbeInitialSupply_packet_parameter_sample
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : Ep × D)
    (hz : parameterTensorModelEquiv (m+1) d z ∈ packet.closedSamples i) : z.1 ∈ packet.Q i.2 := by
  have he := (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
  rw [parameterTensorModelEquiv_symm_apply] at he
  have heP := congrArg Prod.fst he
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z) = z.1 at heP
  rw [← heP]
  exact hz.2.2.1

/-- Algebra between an actually produced full physical error and the exact
normalization used by the immutable repair packet. -/
theorem actualProbeInitialSupply_normalize_packet_error
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given)
    (hmetric : packet.metric = Data.H) (U : P × M → V)
    (C t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (error : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ)
    (herror : error.val = incrementsOriginalMetricError
      (fun z => Real.sqrt (1-(t^10)^2) • packet.referenceMap z) U
      (actualProbeInitialTargetGerm packet hmetric t).val (t^10))
    (hbound : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart
      packet.closedSamples univ packet.closedSamples_compact (fun _ _ hy => hy.1) (t^((6 : ℝ)/5)) 440 error ≤
      C*(t^10*(t^((6 : ℝ)/5)/t^((11 : ℝ)/10))^440+(t^10)^3/t^((6 : ℝ)/5))) :
    ∃ normalized : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ,
      normalized.val = (fun p x => packet.normalizedDefect
        (actualRepairModelFirstDefectFirstMap packet.referenceMap U (t^10)) 10 (t^((6 : ℝ)/5)) p x-Data.H p x) ∧
      parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples
        univ packet.closedSamples_compact (fun _ _ hy => hy.1) (t^((6 : ℝ)/5)) 440 normalized ≤
        C*(t^(30 : ℝ)+t^((24 : ℝ)/5)) := by
  have hF0 : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => packet.referenceMap (p,x)) := by
    intro p
    have href := packet.referenceMap_smooth
    rw [modelWithCornersSelf_prod] at href
    exact href.comp (contMDiff_const.prodMk contMDiff_id)
  have htarget := (actualProbeInitialSupply_target_original_profile packet hmetric t ht ht1).1
  rw [htarget] at herror
  obtain ⟨normalized,hvalue,hnorm⟩ := actualProbeInitialSupply_normalized_original_scale
    Data.atlas packet.parameterFamily.chart packet.closedSamples univ packet.closedSamples_compact
    (fun _ _ hy => hy.1) packet.referenceMap U hF0 C t 440 ht ht1 error herror hbound
  refine ⟨normalized,?_,hnorm⟩
  simpa only [Round3RepairFixedSmoothingPacket.normalizedDefect,actualRepairModelFirstDefectFirstMap,
    hmetric,packet.reference_tensor] using hvalue

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialParameterAtlas
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_parameter_atlas_smooth
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_packet_parameter_sample
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_normalize_packet_error
