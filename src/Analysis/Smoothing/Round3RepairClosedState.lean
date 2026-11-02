import Smoothing.Round3RepairLiteralStage
import Probes.Round3RepairClosedPairRecurrence
import Probes.Round3ParameterWholeRepairStep
import GlobalEmbedding.Offline.IterationScales

/-! Actual closed-domain repair states.  The defect is always computed from
the same current map and the prescribed metric.  The map reserve includes a
remaining-scale envelope, so one actual small increment preserves the C2
entrance without a fictitious unchanged distance bound. -/
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
local instance round3RepairClosedStateChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairClosedStateIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

namespace Round3RepairFixedSmoothingPacket
variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- Only the coverage proof changes; raw cutoff functions are literally the
same, so the closed-domain smoother is exactly the original smoother. -/
def closedParameterPreparation (hK : Data.parameterSet = univ) :
    TensorLocalRawPreparation packet.parameterFamily univ BP0 TP0 Dp :=
  { packet.parameterPreparation with
    plateau_on := fun p _ => packet.parameterPreparation.plateau_on p (by rw [hK]; exact mem_univ _) }

@[simp] theorem closedParameterPreparation_raw (hK : Data.parameterSet = univ) :
    (packet.closedParameterPreparation hK).raw = packet.parameterPreparation.raw := rfl

def closedSamples : Fin Data.atlas.count × Fin Data.parameterCount → Set (Fin (n+d) → ℝ) :=
  incrementsOriginalEvaluation Data.atlas packet.parameterFamily.chart packet.Omega packet.Q univ

def normalizedDefect (G : P × M → Ey) (k : ℕ) (t : ℝ)
    (p : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace IT x) :=
  ((t^k)^2)⁻¹ • (packet.metric p x-inducedMetric (I := IT) (fun y => G (p,y)) x)

def mapDistance (G : P × M → Ey) : ℝ≥0∞ :=
  paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
    (fun z => G z-packet.referenceMap z))
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples

def defectDistance (G : P × M → Ey) (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
    (fun p x => packet.normalizedDefect G k t p x-Data.H p x))
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples

def pairNorm (G : P × M → Ey) (k : ℕ) (t : ℝ) (j : ℕ) : ℝ≥0∞ :=
  parameterLocalOriginalTotalPairWeighted Data.atlas packet.parameterFamily G
    (packet.normalizedDefect G k t) j t packet.closedSamples

theorem closedSamples_compact : ∀ i, IsCompact (packet.closedSamples i) :=
  parameterRound2_originalEvaluation_univ_compact Data.atlas packet.parameterFamily.chart packet.Omega packet.Q
    packet.source_compact packet.parameter_compact packet.source_target packet.parameter_target

theorem originalSamples_eq_closed
    (hK : Data.parameterSet = univ)
    (hOmega : Data.sourceNormDomain = packet.Omega) (hQ : Data.parameterNormDomain = packet.Q) :
    incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet = packet.closedSamples := by
  rw [hOmega,hQ,hK,← packet.chart_eq]
  rfl

end Round3RepairFixedSmoothingPacket

/-- Invariant state for the actual same-domain iteration.  The map and tensor
norms are literal original MAX norms, and the tensor is computed from map. -/
structure Round3RepairClosedState
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (budget epsilon eta : ℝ) (k : ℕ) (t : ℝ) where
  map : P × M → Ey
  smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ map
  map_close : (packet.mapDistance map).toReal ≤ (epsilon/4)*(1-t)
  defect_close : (packet.defectDistance map k t).toReal ≤ eta
  pair_budget : (packet.pairNorm map k t (40*(k+1))).toReal ≤ budget

namespace Round3RepairClosedState
variable {packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket}
  {budget epsilon eta : ℝ} {k : ℕ} {t : ℝ}

/-- A valid current state supplies the literal input to actual SF/SH; it
contains no smoothed-map, smoothed-target, mean or correction hypothesis. -/
def toSmoothingState [CompactSpace M]
    (state : Round3RepairClosedState packet budget epsilon eta k t)
    (s : ℕ) (hk : 10 ≤ k) (hks : k ≤ s) (ht : 0 < t) (ht1 : t ≤ 1) :
    Round3RepairCurrentSmoothingState packet (40*(k+1)) budget :=
  round3RepairLiteralCurrentState packet k s hk hks t ht ht1 state.map state.smooth budget state.pair_budget

theorem mapDistance_finite
    (state : Round3RepairClosedState packet budget epsilon eta k t) : packet.mapDistance state.map ≠ ⊤ := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  exact parameterRound2_paperAtlasCj_finite_of_compact
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => state.map z-packet.referenceMap z))
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    packet.closedSamples_compact (fun _ _ hy => hy.1)
    (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB _ (state.smooth.sub packet.referenceMap_smooth)) 2

theorem pairNorm_finite
    (state : Round3RepairClosedState packet budget epsilon eta k t) (j : ℕ) :
    packet.pairNorm state.map k t j ≠ ⊤ := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hG := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB state.map state.smooth
  have hH := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB state.map state.smooth packet.metric packet.metric_smooth (t^k)
  exact parameterRound2_original_pair_on_compact_finite Data.atlas packet.parameterFamily packet.Omega packet.Q
    packet.source_compact packet.parameter_compact packet.source_target packet.parameter_target
    state.map hG (packet.normalizedDefect state.map k t) hH j t

end Round3RepairClosedState
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairFixedSmoothingPacket.closedParameterPreparation
#print axioms GlobalEmbedding.Continuation.Round3RepairClosedState.toSmoothingState
