import Smoothing.Round3RepairComputedStage

/-! The paper's literal k/s/t scales build the state and satisfy the computed
stage's low-order entrances at one explicit positive threshold.  The threshold
uses fixed smoothing, reference and original linear-functional costs before t
and before the current map.  No SF positivity or C2-bound premise remains. -/
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
local instance round3RepairLiteralChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairLiteralIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- Literal state at either permitted next reserve. The reserve ratio and all
scale order conditions are proved from t, k, s. -/
def round3RepairLiteralCurrentState
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (k s : ℕ) (hk : 10 ≤ k) (hks : k ≤ s) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (oldMap : P × M → Ey) (hOld : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ oldMap)
    (budget : ℝ)
    (hBudget : (parameterLocalOriginalTotalPairWeighted Data.atlas packet.parameterFamily oldMap
      (fun p x => ((t^k)^2)⁻¹ • (packet.metric p x-inducedMetric (I := IT) (fun y => oldMap (p,y)) x))
      (40*(k+1)) t (incrementsOriginalEvaluation Data.atlas packet.parameterFamily.chart
        packet.Omega packet.Q univ)).toReal ≤ budget) :
    Round3RepairCurrentSmoothingState packet (40*(k+1)) budget where
  oldMap := oldMap
  oldMap_smooth := hOld
  ell := t^(11/10 : ℝ)
  t := t
  ell_pos := Real.rpow_pos_of_pos ht _
  ell_le_t := (repair_step_scale_order ht ht1 k hk).2.2.2
  t_le_one := ht1
  delta := t^k
  deltaNext := (t^(6/5 : ℝ))^s
  reserve_ratio := ((round3_repair_literal_low_powers ht ht1 k s hk hks).2).trans ht1
  old_pair_budget := hBudget

private theorem round3_repair_original_zero_profile_scale
    (Data : IncrementsOriginalNativeData n d N M P) (ell : ℝ) :
    incrementsOriginalInputProfileWithLinear Data 0 ell =
      incrementsOriginalInputProfileWithLinear Data 0 1 := by
  simp only [incrementsOriginalInputProfileWithLinear,incrementsOriginalCoreInputProfile,
    paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,pow_zero,one_mul,zero_add]

/-- One positive geometry entrance actually produces the literal new stage.
The old low-order invariants are all that remain: C2 distance to F0 at most
half the geometric tolerance, and C0 normalized defect error below the stated
fixed reserve fraction.  The target belongs to its constructed positive cone
and the smoothed map lies within the full C2 tolerance as conclusions. -/
theorem round3_exists_uniform_literal_positive_stage
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (k : ℕ) (hk : 10 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Data : IncrementsOriginalNativeData n d N M P)
      (reference givenPacket : ℕ → ℝ)
      (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
      (hLinear : IncrementsOriginalLinearSmoothInputs Data)
      (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
      (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
      (budget epsilon ML : ℝ), 0 ≤ budget → 0 < epsilon →
    incrementsOriginalInputProfileWithLinear Data 0 1 ≠ ⊤ →
    (incrementsOriginalInputProfileWithLinear Data 0 1).toReal ≤ ML →
    let L := ‖actualOriginalCoefficientFunctional n‖*ML
    let sigma := round3RepairComputedGeometryThreshold C budget (reference 0) L rho epsilon
    0 < sigma ∧ ∀ (s : ℕ) (hks : k ≤ s) (t : ℝ) (ht : 0 < t) (htSmall : t ≤ sigma),
    ∀ (oldMap : P × M → Ey) (hOld : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ oldMap)
      (hBudget : (parameterLocalOriginalTotalPairWeighted Data.atlas packet.parameterFamily oldMap
        (fun p x => ((t^k)^2)⁻¹ • (packet.metric p x-inducedMetric (I := IT) (fun y => oldMap (p,y)) x))
        (40*(k+1)) t (incrementsOriginalEvaluation Data.atlas packet.parameterFamily.chart
          packet.Omega packet.Q univ)).toReal ≤ budget),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => oldMap z-packet.referenceMap z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => oldMap z-packet.referenceMap z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S).toReal ≤ epsilon/2 →
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
      (fun p x => ((t^k)^2)⁻¹ • (packet.metric p x-inducedMetric (I := IT) (fun y => oldMap (p,y)) x)-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ rho/(4*(L+1)) →
    let ht1 : t ≤ 1 := htSmall.trans (min_le_left _ _)
    let state := round3RepairLiteralCurrentState packet k s hk hks t ht ht1 oldMap hOld budget hBudget
    ∃ out : Round3RepairConstructedPositiveStage packet state rho C (epsilon/2),
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => state.smoothedMap packet z-packet.referenceMap z))
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S).toReal ≤ epsilon := by
  obtain ⟨C,hC,hMake⟩ := round3_exists_uniform_constructed_repair_stage
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius (40*(k+1))
  refine ⟨C,hC,?_⟩
  intro Data reference givenPacket packet hLinear hDecomp rho hReserve budget epsilon ML
    hBudgetNonneg hEpsilon hProfile hML L sigma
  have hRefNonneg : 0 ≤ reference 0 := ENNReal.toReal_nonneg.trans (packet.reference_bound 0)
  have hMLNonneg : 0 ≤ ML := ENNReal.toReal_nonneg.trans hML
  have hL : 0 ≤ L := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hMLNonneg
  refine ⟨round3RepairComputedGeometryThreshold_pos C budget (reference 0) L rho epsilon
    hC hBudgetNonneg hRefNonneg hL hReserve.reserve_pos hEpsilon,?_⟩
  intro s hks t ht htSmall oldMap hOld hBudget S hMapFinite hMap hInherited ht1 state
  have hLow := round3_repair_literal_geometry_threshold C budget (reference 0) L rho epsilon
    hC hBudgetNonneg hRefNonneg hL hReserve.reserve_pos hEpsilon k s hk hks
    t (rho/(4*(L+1))) (epsilon/2) ht htSmall le_rfl le_rfl
  have hRef : (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ reference 0 := by
    rw [packet.reference_tensor,← packet.chart_eq]
    exact packet.reference_bound 0
  have hP : incrementsOriginalInputProfileWithLinear Data 0 state.ell ≠ ⊤ := by
    rw [round3_repair_original_zero_profile_scale]
    exact hProfile
  have hPB : (incrementsOriginalInputProfileWithLinear Data 0 state.ell).toReal ≤ ML := by
    rw [round3_repair_original_zero_profile_scale]
    exact hML
  obtain ⟨out⟩ := hMake Data reference givenPacket packet hLinear hDecomp rho hReserve budget state
    (rho/(4*(L+1))) (reference 0) (epsilon/2) ML hMapFinite hMap hInherited hRef hP hPB hLow.2.2.2
  exact ⟨out,out.map_C2_bound.trans hLow.2.2.1⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_exists_uniform_literal_positive_stage
