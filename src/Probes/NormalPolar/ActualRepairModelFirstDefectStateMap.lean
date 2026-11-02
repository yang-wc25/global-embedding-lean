import NormalPolar.ActualRepairModelFirstDefectIncrementSmooth
import NormalPolar.ActualRepairModelFirstDefectStateTensor
import Smoothing.Round3RepairInitialScaling

/-! The first map is literally sqrt(1-delta^2) F0 + U0. The original joint
C2 displacement includes both contraction and the whole first increment;
the original weighted map budget includes U0 at base two. The increment's
smoothness is recovered from its produced original coordinate germs using
the actual packet cover. -/

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

def actualRepairModelFirstDefectFirstMap (F0 U : P × M → Ey) (delta : ℝ) : P × M → Ey :=
  fun z => Real.sqrt (1-delta^2) • F0 z+U z

theorem actualRepairModelFirstDefect_packet_map_bounds
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hK : Data.parameterSet = univ) (U : P × M → Ey) (j : ℕ) (delta tau C2 CW : ℝ)
    (hcoord : ∀ i, ∃ G : Set (Fin (n+d) → ℝ), IsOpen G ∧ packet.closedSamples i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U i) G)
    (hU2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤ C2)
    (hUW : (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤ CW) :
    let G1 := actualRepairModelFirstDefectFirstMap packet.referenceMap U delta
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ G1 ∧
    (packet.mapDistance G1).toReal ≤ delta^2 *
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+C2 ∧
    (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart G1)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
    (paperAtlasWeighted 2 j tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+CW := by
  intro G1
  have hUs := actualRepairModelFirstDefect_packet_increment_smooth packet hK U hcoord
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  let S := packet.closedSamples
  let f := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap
  let u := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U
  let c := Real.sqrt (1-delta^2)
  let G0 := fun z => c • packet.referenceMap z
  let D0 := fun z => G0 z-packet.referenceMap z
  have hO := parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  have hG0 : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ G0 :=
    ((contDiff_id : ContDiff ℝ ∞ (fun y : Ey => y)).const_smul c).contMDiff.comp packet.referenceMap_smooth
  have hG1 : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ G1 := hG0.add hUs
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hu := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB U hUs
  have hD := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB D0 (hG0.sub packet.referenceMap_smooth)
  have hfinite (F : P × M → Ey) (hs : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart F i) (O i)) (k : ℕ) :=
    parameterRound2_paperAtlasCj_finite_of_compact _ O S hO packet.closedSamples_compact hSO hs k
  refine ⟨hG1,?_,?_⟩
  · have heq : incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => G1 z-packet.referenceMap z) =
        fun i y => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart D0 i y+u i y := by
      funext i y
      change (EuclideanSpace.equiv (Fin N) ℝ) (G0 (incrementsOriginalJointPoint Data.atlas packet.parameterFamily.chart i y)+
        U (incrementsOriginalJointPoint Data.atlas packet.parameterFamily.chart i y)-
        packet.referenceMap (incrementsOriginalJointPoint Data.atlas packet.parameterFamily.chart i y)) = _
      rw [add_sub_right_comm,map_add]
      rfl
    have hadd := parameterRound2_paperAtlasCj_add_le 2
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart D0) u O S hO hSO hD hu
      (hfinite D0 hD 2) (hfinite U hu 2)
    have hsc := round3_repair_initial_scaling_original_bound Data.atlas packet.parameterFamily
      packet.domain.atlas_smooth hB S packet.closedSamples_compact hSO packet.referenceMap packet.referenceMap_smooth 2 delta
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsc
    have hsc2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart D0) O S).toReal ≤
        delta^2*(paperAtlasCj 2 f O S).toReal :=
      hreal.trans_eq (ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg delta) ENNReal.toReal_nonneg))
    change (paperAtlasCj 2 _ O S).toReal ≤ _
    rw [heq]
    exact (actualRepairModelFirstDefect_real_add_bound _ _ _ (hfinite D0 hD 2) (hfinite U hu 2)
      hadd C2 hU2).trans (add_le_add hsc2 le_rfl)
  · have hc : |c| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg delta])
    have hfW := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 j tau f O S (hfinite _ hf (j+2))
    have huW := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 j tau u O S (hfinite U hu (j+2))
    have hsc := parameterRound2_paperAtlasWeighted_smul_le 2 j tau f O S hO hSO hf (hfinite _ hf (j+2)) c
    have hsc' : paperAtlasWeighted 2 j tau (fun i y => c • f i y) O S ≤ paperAtlasWeighted 2 j tau f O S := by
      apply hsc.trans
      have hc' : ENNReal.ofReal |c| ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hc
      simpa only [one_mul] using mul_le_mul_left hc' (paperAtlasWeighted 2 j tau f O S)
    have hscTop := parameterRound2_paperAtlasCj_smul_le (j+2) f O S hO hSO hf (hfinite _ hf (j+2)) c
    have hscFinite := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite _ hf (j+2))) hscTop
    have hadd := parameterRound2_paperAtlasWeighted_add_le 2 j tau (fun i y => c • f i y) u O S hO hSO
      (fun i => (hf i).const_smul c) hu hscFinite (hfinite U hu (j+2))
    have hbound := hadd.trans (add_le_add hsc' le_rfl)
    have heq : incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart G1 =
        fun i y => c • f i y+u i y := by
      funext i y
      simp only [G1,actualRepairModelFirstDefectFirstMap,incrementsOriginalMapCoordinates,map_add,map_smul,c,f,u]
    change (paperAtlasWeighted 2 j tau _ O S).toReal ≤ _
    rw [heq]
    exact actualRepairModelFirstDefect_real_add_bound _ _ _ hfW huW hbound CW hUW

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_packet_map_bounds
