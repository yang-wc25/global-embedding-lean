import NormalPolar.ActualRepairModelFirstDefectStateMap

/-! Assembly of the literal first closed repair state from the two produced
components: the complete U0 original map bounds and the normalized physical
error germ. Only scalar allocations remain. Neither a final mapDistance,
final defectDistance, final pairNorm, nor an existing closed state is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

theorem actualRepairModelFirstDefect_packet_pair_from_components
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hmetric : packet.metric = Data.H) (G : P × M → Ey)
    (hG : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ G) (j : ℕ) (tau CW CE : ℝ)
    (hMap : (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart G)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
      (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+CW)
    (W : Set (P × M))
    (error : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples W)
    (hvalue : error.val = fun p x => packet.normalizedDefect G 10 tau p x-Data.H p x)
    (herror : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart
      packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) tau j error ≤ CE) :
    (packet.pairNorm G 10 tau j).toReal ≤
      (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+CW+CE := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hGM := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB G hG
  have hGH := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB G hG packet.metric packet.metric_smooth (tau^10)
  have hfin := parameterRound2_original_pair_on_compact_finite Data.atlas packet.parameterFamily packet.Omega packet.Q
    packet.source_compact packet.parameter_compact packet.source_target packet.parameter_target
    G hGM (packet.normalizedDefect G 10 tau) hGH j tau
  have hMfin := (ENNReal.add_ne_top.mp hfin).1
  have hHfin := (ENNReal.add_ne_top.mp hfin).2
  have hTensor := (actualRepairModelFirstDefect_packet_tensor_bounds packet hmetric G tau CE j W error hvalue herror).2
  change ENNReal.toReal (_+_) ≤ _
  exact (ENNReal.toReal_add hMfin hHfin).le.trans
    ((add_le_add hMap hTensor).trans_eq (by ring))

def actualRepairModelFirstDefectClosedState
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hK : Data.parameterSet = univ) (hmetric : packet.metric = Data.H)
    (U : P × M → Ey) (delta tau budget epsilon eta C2 CW CE : ℝ)
    (hcoord : ∀ i, ∃ G : Set (Fin (n+d) → ℝ), IsOpen G ∧ packet.closedSamples i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U i) G)
    (hU2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤ C2)
    (hUW : (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤ CW)
    (W : Set (P × M))
    (error : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples W)
    (hvalue : error.val = fun p x => packet.normalizedDefect
      (actualRepairModelFirstDefectFirstMap packet.referenceMap U delta) 10 tau p x-Data.H p x)
    (herror : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart
      packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) tau 440 error ≤ CE)
    (hMapPaid : delta^2 *
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+C2 ≤
      (epsilon/4)*(1-tau))
    (hErrorPaid : CE ≤ eta)
    (hPairPaid :
      (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+
      (paperAtlasWeighted 0 440 tau (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+CW+CE ≤ budget) :
    Round3RepairClosedState packet budget epsilon eta 10 tau := by
  have hMap := actualRepairModelFirstDefect_packet_map_bounds packet hK U 440 delta tau C2 CW hcoord hU2 hUW
  refine ⟨actualRepairModelFirstDefectFirstMap packet.referenceMap U delta,
    hMap.1,hMap.2.1.trans hMapPaid,?_,?_⟩
  · exact (actualRepairModelFirstDefect_packet_tensor_bounds packet hmetric _ tau CE 440 W error hvalue herror).1.trans hErrorPaid
  · exact (actualRepairModelFirstDefect_packet_pair_from_components packet hmetric _ hMap.1 440 tau CW CE
      hMap.2.2 W error hvalue herror).trans hPairPaid

@[simp] theorem actualRepairModelFirstDefectClosedState_map
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hK : Data.parameterSet = univ) (hmetric : packet.metric = Data.H)
    (U : P × M → Ey) (delta tau budget epsilon eta C2 CW CE : ℝ)
    (hcoord hU2 hUW W error hvalue herror hMapPaid hErrorPaid hPairPaid) :
    (actualRepairModelFirstDefectClosedState packet hK hmetric U delta tau budget epsilon eta C2 CW CE
      hcoord hU2 hUW W error hvalue herror hMapPaid hErrorPaid hPairPaid).map =
      actualRepairModelFirstDefectFirstMap packet.referenceMap U delta := rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefectClosedState
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefectClosedState_map
