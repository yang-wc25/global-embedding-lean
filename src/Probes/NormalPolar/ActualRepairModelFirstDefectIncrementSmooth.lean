import NormalPolar.ActualRepairModelFirstDefectIncrementNorms
import Smoothing.Round3RepairClosedBuffers

/-! The local regularity produced from the actual raw increment is global
on the original closed parameter setting. Coverage is the packet's proven
open-buffer coverage; no extra sample-cover premise is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff
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

theorem actualRepairModelFirstDefect_packet_increment_smooth
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hK : Data.parameterSet = univ) (U : P × M → Ey)
    (hcoord : ∀ i, ∃ G : Set (Fin (n+d) → ℝ), IsOpen G ∧ packet.closedSamples i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U i) G) :
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ U := by
  rw [modelWithCornersSelf_prod]
  intro z
  obtain ⟨i,hp,hx,hz⟩ := packet.closedBuffer_cover hK z
  obtain ⟨G,hG,hSG,hGO,hUG⟩ := hcoord i
  rw [packet.chart_eq] at hUG
  exact round3_repair_original_map_contMDiffAt_of_coordinate_germ Data packet.domain U i G hG hUG z hp hx
    (hSG (packet.closedBuffer_subset_samples i hz))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_packet_increment_smooth
