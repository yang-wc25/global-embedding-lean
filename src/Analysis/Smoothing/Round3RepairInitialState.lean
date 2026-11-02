import Smoothing.Round3RepairInitialScaling
import Probes.Round3RepairReferenceEnvelope

/-! Actual repair entrance (6.9), at order 440 for the tensor and 442 for
the reference map.  The initial scale and target radius precede the target
metric.  The initial map is the literal square-root contraction and its
normalized defect, C2 envelope and closed-domain weighted budget are all
proved internally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
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
local instance round3InitialStateChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3InitialStateIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

namespace Round3RepairFixedSmoothingPacket
variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- Replace only the prescribed metric; all reference data, cutoffs,
sampling sets, smoothing kernels and their constants remain literal. -/
def withMetric
    (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (hSym : ∀ p x, (metric p x).IsSymm)
    (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
      packet.parameterFamily.chart metric i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)) :
    Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket :=
  { packet with metric := metric, metric_symmetric := hSym, metric_smooth := hSmooth }

@[simp] theorem withMetric_self :
    packet.withMetric packet.metric packet.metric_symmetric packet.metric_smooth=packet := rfl

end Round3RepairFixedSmoothingPacket

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- The actual original repair initial state, with the initial scale fixed
before the target.  There is no assumed initial state and no target norm
above order 440.  All norms are on the same closed Omega/Q evaluation set
used by the subsequent repair recurrence. -/
theorem round3_repair_original_initial_closed_state
    (budget epsilon eta cap : ℝ)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hcap : 0 < cap)
    (hFixed : round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ (1/2 : ℝ) ∧ t0 ≤ cap ∧
    ∃ targetRadius : ℝ, 0 < targetRadius ∧
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
  classical
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  let C := (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas
    packet.parameterFamily.chart packet.referenceMap)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hscaleCap : 0 < epsilon/(8*(C+1)) := div_pos hepsilon (by positivity)
  have hbudget : 4 *
      ((paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+
       (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
         (fun p x => inducedMetric (I := IT) (fun y => packet.referenceMap (p,y)) x))
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal) < budget := by
    unfold round3RepairReferenceLowBase at hFixed
    rw [packet.reference_tensor] at hFixed
    linarith
  have hbudget0 : 0 < budget := by
    have hn : 0 ≤ round3RepairReferenceLowBase packet :=
      add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    linarith
  obtain ⟨t0,ht0,htHalf,htCap,targetRadius,hRadius,hInitial⟩ :=
    parameterRound2_exists_original_440_initialization Data.atlas packet.parameterFamily
      packet.domain.atlas_smooth hB packet.Omega packet.Q packet.source_compact packet.parameter_compact
      packet.source_target packet.parameter_target packet.referenceMap packet.referenceMap_smooth
      budget eta (min cap (epsilon/(8*(C+1)))) heta (lt_min hcap hscaleCap) hbudget
  refine ⟨t0,ht0,htHalf,htCap.trans (min_le_left _ _),targetRadius,hRadius,?_⟩
  intro metric hSym hSmooth hError
  have hError' := hError
  rw [packet.reference_tensor] at hError'
  have hInit := hInitial metric hSmooth hError'
  dsimp only at hInit
  let G0 : P × M → Ey := fun z => Real.sqrt (1-(t0^10)^2) • packet.referenceMap z
  let changed := packet.withMetric metric hSym hSmooth
  have hmap : (changed.mapDistance G0).toReal ≤ (epsilon/4)*(1-t0) := by
    exact round3_repair_initial_scaling_C2_envelope Data.atlas packet.parameterFamily
      packet.domain.atlas_smooth hB packet.closedSamples packet.closedSamples_compact
      (fun _ _ hy => hy.1) packet.referenceMap packet.referenceMap_smooth hepsilon ht0.le htHalf
      (htCap.trans (min_le_right _ _))
  have hdefect : (changed.defectDistance G0 10 t0).toReal ≤ eta := by
    change (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
      (fun p x => ((t0^10)^2)⁻¹ •
        (metric p x-inducedMetric (I := IT) (fun y => G0 (p,y)) x)-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤ eta
    rw [packet.reference_tensor]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hInit.2.2.2.2.2
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ eta/2)] at h
    exact h.trans (by linarith)
  have hpair : (changed.pairNorm G0 10 t0 (40*(10+1))).toReal ≤ budget := by
    change (parameterLocalOriginalTotalPairWeighted Data.atlas packet.parameterFamily G0
      (fun p x => ((t0^10)^2)⁻¹ •
        (metric p x-inducedMetric (I := IT) (fun y => G0 (p,y)) x)) 440 t0 packet.closedSamples).toReal ≤ budget
    exact hInit.2.2.2.2.1.trans (by linarith)
  let initial : Round3RepairClosedState changed budget epsilon eta 10 t0 :=
    { map := G0, smooth := hInit.2.1, map_close := hmap, defect_close := hdefect, pair_budget := hpair }
  refine ⟨initial,?_,?_⟩
  · change (fun z => Real.sqrt (1-(t0^10)^2) • packet.referenceMap z)=_
    rw [← pow_mul]
  · intro p x
    change ((t0^10)^2)⁻¹ •
      (metric p x-inducedMetric (I := IT) (fun y => G0 (p,y)) x)=_
    rw [packet.reference_tensor]
    simpa only [G0, ← pow_mul] using hInit.1 p x

/-- Specialization to the prescribed metric of the packet.  This is the
direct entrance consumed by the actual infinite repair construction. -/
theorem round3_repair_fixed_metric_initial_closed_state
    (budget epsilon eta cap : ℝ)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hcap : 0 < cap)
    (hFixed : round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ (1/2 : ℝ) ∧ t0 ≤ cap ∧
    ∃ targetRadius : ℝ, 0 < targetRadius ∧
    ∀ (_hError : paperAtlasCj 440 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
      (fun p x => packet.metric p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal targetRadius),
    ∃ initial : Round3RepairClosedState packet budget epsilon eta 10 t0,
      initial.map=(fun z => Real.sqrt (1-t0^20) • packet.referenceMap z) ∧
      ∀ p x, packet.normalizedDefect initial.map 10 t0 p x =
        Data.H p x+(t0^20)⁻¹ • (packet.metric p x-Data.H p x) := by
  obtain ⟨t0,ht0,htHalf,htCap,targetRadius,hRadius,hInitial⟩ :=
    round3_repair_original_initial_closed_state packet budget epsilon eta cap hepsilon heta hcap hFixed
  refine ⟨t0,ht0,htHalf,htCap,targetRadius,hRadius,?_⟩
  intro hError
  simpa only [Round3RepairFixedSmoothingPacket.withMetric_self] using
    hInitial packet.metric packet.metric_symmetric packet.metric_smooth hError

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_original_initial_closed_state
#print axioms GlobalEmbedding.Continuation.round3_repair_fixed_metric_initial_closed_state
