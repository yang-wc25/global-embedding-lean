import Smoothing.Round3RepairComputedStage
import Probes.Round4ParameterLowLocalPairTail

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
local instance round4ParameterPositiveChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterPositiveIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

/-- The uniform low-order cost precedes the reference packet and current
state.  Actual old-map and defect control produce the literal computed stage,
its original domain/decomposition/reserve, and its original C2 closeness. -/
theorem round4Parameter_actual_constructed_positive_stage
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    let C := 2*round4PreparedPairConstant n d radius hradius BS0 TS0 BP0 TP0 Ds Dp 0 r
    0 ≤ C ∧ ∀ (Data : IncrementsOriginalNativeData n d N M P)
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
  let C := 2*round4PreparedPairConstant n d radius hradius BS0 TS0 BP0 TP0 Ds Dp 0 r
  obtain ⟨hC,hlow⟩ := round4Parameter_actual_local_low_pair_tail
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨hC,?_⟩
  intro Data reference givenPacket packet hLinear hDecomp rho hReserve budget state
    inherited refBound mapInherited ML S hMapFinite hMap hInherited hRefBound hProfile hML hSmall
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hS : ∀ i, S i ⊆ round3OuterOriginalEvaluation Data.atlas packet.parameterFamily Data.parameterSet i := by
    intro i y hy
    change y ∈ round3OuterOriginalEvaluation Data.atlas packet.parameterFamily Data.parameterSet i
    unfold round3OuterOriginalEvaluation
    rw [packet.chart_eq]
    exact ⟨hy.1,hy.2.2.2⟩
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i := by
    rw [packet.chart_eq]
    exact fun _ _ hy => hy.1
  have hu := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB state.oldMap state.oldMap_smooth
  let SH := tensorLocalParameterSmoothing Data.atlas packet.parameterFamily packet.domain.atlas_smooth
    (volume : Measure (Ep × Es)) (fixedSmoothingKernel (volume : Measure (Ep × Es)) radius hradius r)
    state.ell (parameterLocalProductCutoff Data.atlas packet.parameterFamily
      (squareNormalizedCutoff packet.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff packet.parameterPreparation.raw)) (state.normalizedDefect packet)
  let SF := state.smoothedMap packet
  let Target := state.computedTarget packet
  have hp := hlow Data.parameterCount Data.atlas packet.parameterFamily packet.domain.atlas_smooth hB
    Data.parameterSet packet.sourcePreparation packet.parameterPreparation packet.buffer
    packet.Omega packet.Q packet.source_compact packet.parameter_compact packet.source_target
    packet.parameter_target packet.source_sampling packet.parameter_sampling S hS
    state.ell state.t state.ell_pos state.ell_le_t state.t_le_one state.oldMap hu
    (state.normalizedDefect packet) (state.normalizedDefect_smooth packet) budget state.old_pair_budget
  dsimp only at hp
  have hSH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart SH i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) := hp.2.1
  have hRef : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) := by
    rw [packet.reference_tensor]
    exact parameterRound2_inducedMetric_originalCoordinates_contDiffOn Data.atlas
      packet.parameterFamily.chart packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hRefs : ∀ p x, (Data.H p x).IsSymm := by
    rw [packet.reference_tensor]
    exact fun p x => (inducedMetric_isPosSemidef (I := IT) (fun y => packet.referenceMap (p,y)) x).isSymm
  have hSHs : ∀ p x, (SH p x).IsSymm := fun p x =>
    tensorFamilySmoothing_isSymm (parameterLocalProductFamily Data.atlas packet.parameterFamily)
      (volume : Measure (Ep × Es)) (fixedSmoothingKernel (volume : Measure (Ep × Es)) radius hradius r)
      state.ell (parameterLocalProductCutoff Data.atlas packet.parameterFamily
        (squareNormalizedCutoff packet.sourcePreparation.raw)
        (tensorLocalNormalizedCutoff packet.parameterPreparation.raw))
      (tensorLocalParameterFrame Data.atlas packet.parameterFamily packet.domain.atlas_smooth)
      (fun z => state.normalizedDefect packet z.1 z.2)
      (fun z => state.normalizedDefect_symmetric packet z.1 z.2) (p,x)
  have hsum : paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => state.oldMap z-SF z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
        (fun p x => state.normalizedDefect packet p x-SH p x))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S ≠ ⊤ := by
    simpa only [SF,SH,Round3RepairCurrentSmoothingState.smoothedMap,
      parameterLocalOriginalTotalPairWeighted,paperAtlasWeighted,
      Finset.sum_range_one,pow_zero,zero_add,one_mul] using hp.2.2.1
  have hsumBound : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => state.oldMap z-SF z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
        (fun p x => state.normalizedDefect packet p x-SH p x))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S).toReal ≤
      C*budget*(state.ell/state.t)^r := by
    simpa only [C,SF,SH,Round3RepairCurrentSmoothingState.smoothedMap,
      parameterLocalOriginalTotalPairWeighted,paperAtlasWeighted,
      Finset.sum_range_one,pow_zero,zero_add,one_mul] using hp.2.2.2
  have hmap := (ENNReal.toReal_mono hsum (le_add_right (le_refl _))).trans hsumBound
  have htensor := (ENNReal.toReal_mono hsum (le_add_left (le_refl _))).trans hsumBound
  have htarget := round3_original_target_C0_from_smoothing_error Data.atlas packet.parameterFamily.chart S
    packet.samples_compact hSO (state.normalizedDefect packet) SH Data.H
    (state.normalizedDefect_smooth packet) hSH hRef
    (state.normalizedDefect_symmetric packet) hSHs hRefs state.ell
    ((state.deltaNext/state.delta)^2) (C*budget*(state.ell/state.t)^r) inherited refBound (sq_nonneg _)
    htensor (by simpa only [packet.chart_eq] using hInherited)
    (by simpa only [packet.chart_eq] using hRefBound)
  have hTargetSmooth : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Target i)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i) := by
    rw [← packet.chart_eq]
    exact fun i => (hSH i).sub ((hRef i).const_smul ((state.deltaNext/state.delta)^2))
  have hTargetSymm : ∀ p ∈ Data.parameterOpen, ∀ x, (Target p x).IsSymm :=
    fun p _ x => (hSHs p x).sub ((hRefs p x).smul _)
  have hTF : paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => Target p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ := by
    rw [← packet.chart_eq]
    exact htarget.1
  have hTB : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => Target p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤
      C*budget*(state.ell/state.t)^r+inherited+(state.deltaNext/state.delta)^2*refBound := by
    rw [← packet.chart_eq]
    exact htarget.2
  have hGerm : ∀ i, ∃ O : Set (Fin (n+d) → ℝ), IsOpen O ∧ S i ⊆ O ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Target i) O :=
    fun i => ⟨incrementsOriginalDifferentiation Data.atlas Data.parameterChart i,
      parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i,
      fun _ (hy : _ ∈ S i) => hy.1,hTargetSmooth i⟩
  have hRefGerm : ∀ i, ∃ O : Set (Fin (n+d) → ℝ), IsOpen O ∧ S i ⊆ O ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.reference i) O := by
    intro i
    refine ⟨incrementsOriginalDifferentiation Data.atlas Data.parameterChart i,
      parameterRound2_originalDifferentiation_open Data.atlas Data.parameterChart i,
      fun _ hy => hy.1,?_⟩
    rw [packet.reference_eq,← packet.chart_eq]
    exact hRef i
  obtain ⟨U,hU,hKU,hUW,hDomain,hQual,hRes⟩ :=
    round3_original_local_retarget_positive_cone_of_C0 Data packet.domain hLinear hDecomp rho hReserve
      Target hTargetSymm hGerm hRefGerm state.ell ML
      (C*budget*(state.ell/state.t)^r+inherited+(state.deltaNext/state.delta)^2*refBound)
      hProfile hML hTF hTB hSmall
  have hSF := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB SF hp.1
  have hF0 := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hControl := round3_original_reference_C2_from_tail
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart state.oldMap)
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart SF)
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) S
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart) hSO hu hSF hF0
    (ENNReal.add_ne_top.mp hsum).1 hMapFinite (C*budget*(state.ell/state.t)^r) mapInherited hmap hMap
  refine ⟨⟨U,hU,hKU,hUW,?_,?_,?_,hp.1,hControl.1,hControl.2⟩⟩
  · exact { source_dim := hDomain.source_dim
            target_dim := hDomain.target_dim
            parameter_open := hDomain.parameter_open
            parameter_compact := hDomain.parameter_compact
            parameter_subset := hDomain.parameter_subset
            atlas_smooth := hDomain.atlas_smooth
            parameter_charts_smooth := hDomain.parameter_charts_smooth
            source_norm_subset := hDomain.source_norm_subset
            source_inner_norm := hDomain.source_inner_norm
            parameter_norm_subset := hDomain.parameter_norm_subset
            parameter_cover := hDomain.parameter_cover
            primary_open := hDomain.primary_open
            cutoff_support_local := hDomain.cutoff_support_local }
  · exact { fiber_open := hQual.fiber_open
            H_symmetric := hQual.H_symmetric
            reference_symmetric := hQual.reference_symmetric
            H_mem := hQual.H_mem
            reference_mem := hQual.reference_mem
            decomposition := hQual.decomposition
            argument_positive := hQual.argument_positive }
  · exact ⟨hRes.reserve_pos,hRes.lower⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_actual_constructed_positive_stage
