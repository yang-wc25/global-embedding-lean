import Smoothing.Round3RepairCurrentState
import Smoothing.Round3OuterGeometryThreshold

/-! The actual current state produces a genuine next smoothing stage.
The computed tensor's cone, reserve and domain conditions come from the same
SF/SH pair.  The fixed original packet remains literal.  Neither a successful
stage nor any smoothed derivative bound is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairComputedChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairComputedIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

structure Round3RepairConstructedPositiveStage
    {Data : IncrementsOriginalNativeData n d N M P}
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference givenPacket : ℕ → ℝ}
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    {r : ℕ} {budget : ℝ} (state : Round3RepairCurrentSmoothingState packet r budget)
    (rho C mapInherited : ℝ) where
  parameterOpen : Set P
  isOpen : IsOpen parameterOpen
  contains_parameters : Data.parameterSet ⊆ parameterOpen
  within_reference : parameterOpen ⊆ Data.parameterOpen
  domain : IncrementsOriginalDomainConditions (state.computedData packet parameterOpen (rho/4))
  decomposition : IncrementsOriginalQualitativeDecompositionInputs
    (state.computedData packet parameterOpen (rho/4))
  reserve : IncrementsOriginalDecompositionReserveInputs
    (state.computedData packet parameterOpen (rho/4)) (rho/4)
  map_smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (state.smoothedMap packet)
  map_C2_finite : paperAtlasCj 2
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => state.smoothedMap packet z-packet.referenceMap z))
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet) ≠ ⊤
  map_C2_bound : (paperAtlasCj 2
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => state.smoothedMap packet z-packet.referenceMap z))
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)).toReal ≤
        C*budget*(state.ell/state.t)^r+mapInherited

namespace Round3RepairConstructedPositiveStage
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  {packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket}
  {r : ℕ} {budget : ℝ} {state : Round3RepairCurrentSmoothingState packet r budget}
  {rho C mapInherited : ℝ}

def stage (out : Round3RepairConstructedPositiveStage packet state rho C mapInherited) :
    Round3RepairOriginalSmoothingStage (state.computedData packet out.parameterOpen (rho/4))
      BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket :=
  state.toStage packet out.parameterOpen (rho/4)

end Round3RepairConstructedPositiveStage

/-- The uniform low-order cost precedes the reference packet and current
state.  Actual old-map and defect control produce the literal computed stage,
its original domain/decomposition/reserve, and its original C2 closeness. -/
theorem round3_exists_uniform_constructed_repair_stage
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Data : IncrementsOriginalNativeData n d N M P)
      (reference givenPacket : ℕ → ℝ)
      (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
      (hLinear : IncrementsOriginalLinearSmoothInputs Data)
      (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
      (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
      (budget : ℝ) (state : Round3RepairCurrentSmoothingState packet r budget)
      (inherited refBound mapInherited ML : ℝ),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => state.oldMap z-packet.referenceMap z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => state.oldMap z-packet.referenceMap z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S).toReal ≤ mapInherited →
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
      (fun p x => state.normalizedDefect packet p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ inherited →
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ refBound →
    incrementsOriginalInputProfileWithLinear Data 0 state.ell ≠ ⊤ →
    (incrementsOriginalInputProfileWithLinear Data 0 state.ell).toReal ≤ ML →
    ‖actualOriginalCoefficientFunctional n‖ * ML *
      (C*budget*(state.ell/state.t)^r+inherited+
        (state.deltaNext/state.delta)^2*refBound) ≤ rho/2 →
    Nonempty (Round3RepairConstructedPositiveStage packet state rho C mapInherited) := by
  obtain ⟨C,hC,hActual⟩ := round3Outer_exists_uniform_computed_repair_control
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨C,hC,?_⟩
  intro Data reference givenPacket packet hLinear hDecomp rho hReserve budget state
    inherited refBound mapInherited ML S hMapFinite hMap hInherited hRef hProfile hML hSmall
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hu := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB state.oldMap state.oldMap_smooth
  have h := hActual Data packet.domain hLinear hDecomp rho hReserve
    packet.parameterFamily packet.chart_eq packet.sourcePreparation packet.parameterPreparation packet.buffer
    packet.Omega packet.Q packet.source_compact packet.parameter_compact packet.source_target
    packet.parameter_target packet.source_sampling packet.parameter_sampling packet.samples_compact
    state.ell state.t state.ell_pos state.ell_le_t state.t_le_one state.oldMap hu
    (state.normalizedDefect packet) (state.normalizedDefect_smooth packet) (state.normalizedDefect_symmetric packet)
    packet.referenceMap packet.referenceMap_smooth packet.reference_tensor packet.reference_eq
    ((state.deltaNext/state.delta)^2) inherited refBound mapInherited budget ML (sq_nonneg _)
    hMapFinite hMap hInherited hRef state.old_pair_budget hProfile hML hSmall
  dsimp only at h
  obtain ⟨hSmooth,hC2Finite,hC2,hTailFinite,hTail,U,hU,hKU,hUW,hd,hdec,hres⟩ := h
  exact ⟨⟨U,hU,hKU,hUW,hd,hdec,hres,hSmooth,hC2Finite,hC2⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_exists_uniform_constructed_repair_stage
