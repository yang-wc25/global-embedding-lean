import Smoothing.Round3RepairClosedState
import Smoothing.Round3RepairOriginalLocalSmooth
import GlobalEmbedding.Offline.PaperStageChartBridge

/-! The fixed convolution sampling domains contain actual open buffers.
On the whole physical parameter manifold they cover every point, using the
actual parameter plateau and the original source atlas.  No compact sampling
domain is identified with an entire chart target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
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
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairClosedBufferChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairClosedBufferIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

namespace Round3RepairFixedSmoothingPacket
variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- The genuine common open buffer used by every actual iteration. -/
def closedBuffer (i : Fin Data.atlas.count × Fin Data.parameterCount) : Set (Fin (n+d) → ℝ) :=
  (parameterTensorModelEquiv n d).symm ⁻¹'
    (tensorLocalSamplingCoordinates packet.parameterFamily i.2 ×ˢ bufferedSamplingCoordinates Data.atlas i.1)

theorem closedBuffer_open (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    IsOpen (packet.closedBuffer i) :=
  ((tensorLocalSamplingCoordinates_open packet.parameterFamily i.2).prod
    (bufferedSamplingCoordinates_open Data.atlas i.1)).preimage (parameterTensorModelEquiv n d).symm.continuous

theorem closedBuffer_subset_samples (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    packet.closedBuffer i ⊆ packet.closedSamples i := by
  intro y hy
  change (parameterTensorModelEquiv n d).symm y ∈
    tensorLocalSamplingCoordinates packet.parameterFamily i.2 ×ˢ bufferedSamplingCoordinates Data.atlas i.1 at hy
  rw [parameterTensorModelEquiv_symm_apply] at hy
  exact ⟨⟨bufferedSampling_subset_target Data.atlas i.1 hy.2,
    tensorLocalSampling_subset_target packet.parameterFamily i.2 hy.1⟩,
    packet.source_sampling i.1 hy.2,packet.parameter_sampling i.2 hy.1,mem_univ _⟩

/-- Every physical point lies in one of these same fixed open buffers. -/
theorem closedBuffer_cover (hK : Data.parameterSet = univ) (z : P × M) :
    ∃ i : Fin Data.atlas.count × Fin Data.parameterCount,
      z.1 ∈ (Data.parameterChart i.2).source ∧ z.2 ∈ (Data.atlas.chart i.1).source ∧
      parameterRound2_originalForwardCoordinates Data i z ∈ packet.closedBuffer i := by
  obtain ⟨a,ha⟩ := Data.atlas.cover z.2
  obtain ⟨b,hb⟩ := packet.parameterPreparation.plateau_on z.1 (by rw [hK]; exact mem_univ _)
  have hpInner : z.1 ∈ packet.parameterFamily.inner b :=
    packet.parameterPreparation.inner_support b (subset_tsupport _ (by rw [Function.mem_support,hb]; norm_num))
  have hp : z.1 ∈ (packet.parameterFamily.chart b).source := packet.parameterFamily.inner_subset b hpInner
  have hx : z.2 ∈ (Data.atlas.chart a).source := Data.atlas.inner_subset a ha
  have hpSample := tensorLocalInner_subset_sampling packet.parameterFamily b
    (tensorLocalInner_mem packet.parameterFamily b hpInner)
  have hxInner : Data.atlas.chart a z.2 ∈ bufferedInnerCoordinates Data.atlas a :=
    ⟨(Data.atlas.chart a).map_source hx,by simpa only [Set.mem_preimage,(Data.atlas.chart a).left_inv hx] using ha⟩
  have hxSample := bufferedInner_subset_sampling Data.atlas a hxInner
  refine ⟨(a,b),?_,hx,?_⟩
  · simpa only [← packet.chart_eq] using hp
  · change (parameterTensorModelEquiv n d).symm
      (parameterTensorModelEquiv n d (Data.parameterChart b z.1,Data.atlas.chart a z.2)) ∈
        tensorLocalSamplingCoordinates packet.parameterFamily b ×ˢ bufferedSamplingCoordinates Data.atlas a
    rw [(parameterTensorModelEquiv n d).symm_apply_apply,← packet.chart_eq]
    exact ⟨hpSample,hxSample⟩

/-- Restriction to this buffer preserves the original sorted-partial bound
with constant one.  It is the actual map, and the chart maximum is unchanged. -/
theorem closedBuffer_map_bound (f : P × M → Ey)
    (hf : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ f)
    (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    paperCoordinateCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart f i)
      (packet.closedBuffer i) (packet.closedBuffer i) ≤
    paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart f)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  exact (paperCoordinateCj_restrict_buffer j
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
    (fun _ hy => hy.1) (packet.closedBuffer_open i) (packet.closedBuffer_subset_samples i)
    (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB f hf i)).trans (le_iSup
        (fun i => paperCoordinateCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart f i)
          (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) i)

end Round3RepairFixedSmoothingPacket
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairFixedSmoothingPacket.closedBuffer_cover
#print axioms GlobalEmbedding.Continuation.Round3RepairFixedSmoothingPacket.closedBuffer_map_bound
