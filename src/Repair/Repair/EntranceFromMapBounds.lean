import Repair.EntranceInitial
import Repair.EntranceReferenceMetric

/-!
# Uniform finite entrance from original reference map bounds alone

The metric of the reference map is not supplied with separate estimates.
Its two required bounds are produced from the original map C2 and C442
bounds.  One numerical t0 and epsilon* therefore work for every map in
that numerical class, with exactly the target's C440 entrance condition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def repairEntranceLowFromMap (n d N : ℕ) (C2 : ℝ) : ℝ :=
  C2+repairEntranceMetricCost n d N 0*C2^2

def repairEntranceHighFromMap (n d N : ℕ) (C442 : ℝ) : ℝ :=
  C442+repairEntranceMetricCost n d N 440*C442^2

theorem repairEntranceLowFromMap_nonneg (n d N : ℕ) {C2 : ℝ} (hC2 : 0 ≤ C2) :
    0 ≤ repairEntranceLowFromMap n d N C2 :=
  add_nonneg hC2 (mul_nonneg (repairEntranceMetricCost_nonneg _ _ _ _) (sq_nonneg _))

theorem repairEntranceHighFromMap_nonneg (n d N : ℕ) {C442 : ℝ} (hC442 : 0 ≤ C442) :
    0 ≤ repairEntranceHighFromMap n d N C442 :=
  add_nonneg hC442 (mul_nonneg (repairEntranceMetricCost_nonneg _ _ _ _) (sq_nonneg _))

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
private local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- The low baseline used by every subsequent actual repair recurrence
is paid by the same original reference C2 bound. -/
theorem repairEntrance_reference_low_bound
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hMap2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
      packet.closedSamples).toReal ≤ C2) :
    round3RepairReferenceLowBase packet ≤ repairEntranceLowFromMap (m+1) d N C2 := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hfinite := parameterRound2_paperAtlasCj_finite_of_compact
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    packet.closedSamples_compact (fun _ _ hy => hy.1) hf 2
  have hm := repairEntrance_inducedMetric_Cj_le Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.closedSamples (fun _ _ hy => hy.1)
    packet.referenceMap packet.referenceMap_smooth 0 C2 hC2 hfinite hMap2
  unfold round3RepairReferenceLowBase
  rw [packet.reference_tensor]
  exact add_le_add hMap2 hm.2

/-- Original map C2/C442 upper bounds produce the uniform repair entrance.
All target-dependent work starts only after the numerical scale and radius
have been determined.  The target requires no derivatives above 440. -/
theorem repairEntrance_uniform_from_map_bounds
    (budget epsilon eta cap C2 C442 : ℝ)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hcap : 0 < cap)
    (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442)
    (hFixed : repairEntranceLowFromMap (m+1) d N C2+epsilon/4 ≤ budget/4)
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hMap2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
      packet.closedSamples).toReal ≤ C2)
    (hMap442 : (paperAtlasCj 442 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
      packet.closedSamples).toReal ≤ C442) :
    let t0 := repairEntranceScale budget epsilon cap
      (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442)
    let targetRadius := repairEntranceMetricRadius t0 budget eta
    0 < t0 ∧ t0 ≤ (1/2 : ℝ) ∧ t0 ≤ cap ∧ 0 < targetRadius ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    paperAtlasCj 440 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
      (fun p x => metric p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal targetRadius →
    ∃ initial : Round3RepairClosedState (packet.withMetric metric hSym hSmooth) budget epsilon eta 10 t0,
      initial.map=(fun z => Real.sqrt (1-t0^20) • packet.referenceMap z) ∧
      ∀ p x, (packet.withMetric metric hSym hSmooth).normalizedDefect initial.map 10 t0 p x =
        Data.H p x+(t0^20)⁻¹ • (metric p x-Data.H p x) := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hFinite (j : ℕ) := parameterRound2_paperAtlasCj_finite_of_compact
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    packet.closedSamples_compact (fun _ _ hy => hy.1) hf j
  have hMetric0 := repairEntrance_inducedMetric_Cj_le Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.closedSamples (fun _ _ hy => hy.1)
    packet.referenceMap packet.referenceMap_smooth 0 C2 hC2 (hFinite 2) hMap2
  have hMetric440 := repairEntrance_inducedMetric_Cj_le Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.closedSamples (fun _ _ hy => hy.1)
    packet.referenceMap packet.referenceMap_smooth 440 C442 hC442 (hFinite 442) hMap442
  apply repairEntrance_uniform_initial_closed_state budget epsilon eta cap
    (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442)
    hepsilon heta hcap (repairEntranceLowFromMap_nonneg _ _ _ hC2)
    (repairEntranceHighFromMap_nonneg _ _ _ hC442) hFixed packet
  · unfold round3RepairReferenceLowBase
    rw [packet.reference_tensor]
    exact add_le_add hMap2 hMetric0.2
  · rw [packet.reference_tensor]
    exact add_le_add hMap442 hMetric440.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_uniform_from_map_bounds
