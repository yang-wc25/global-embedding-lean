import Smoothing.Round3RepairClosedState

/-! The original C2 reserve is preserved by the very same actual increment.
The remaining-scale envelope makes this a genuine invariant of the iterated
map.  The increment estimate is taken from its joint all-order conclusion;
no separate low-order displacement premise is accepted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
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
local instance round3RepairReferenceEnvelopeChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairReferenceEnvelopeIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- Actual same-U displacement gives the fixed-reference C2 reserve for the
next state.  The threshold is a finite explicitly named numerical cost. -/
theorem round3_repair_same_increment_reference_envelope
    {budget epsilon eta t : ℝ} {k : ℕ}
    (state : Round3RepairClosedState packet budget epsilon eta k t)
    (hk : 10 ≤ k) (ht : 0 < t) (htsmall : t ≤ (1/2 : ℝ)^5)
    (heps : 0 ≤ epsilon) (F U : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (q : ℕ) (ell : ℝ) (Cmap Cmetric : ℕ → ℝ) (hCmap : ∀ j, 0 ≤ Cmap j)
    (hout : Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart
      packet.closedSamples univ F U H q (t^k) (t^(6/5 : ℝ)) ell Cmap Cmetric)
    (hsmall : t ≤ epsilon/(8*(Cmap (k/2)+1))) :
    (packet.mapDistance (fun z => state.map z+U z)).toReal ≤
      (epsilon/4)*(1-t^(6/5 : ℝ)) := by
  have ht1 : t ≤ 1 := by norm_num at htsmall; linarith
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hU : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ U := by
    have h := contMDiffOn_univ.mp hout.joint_smooth
    rw [modelWithCornersSelf_prod]
    exact h
  have hUbudget := round3Parameter_same_increment_growing_order_budget
    Data.atlas packet.parameterFamily.chart packet.closedSamples univ F U H q (t^k)
    (t^(6/5 : ℝ)) ell Cmap Cmetric hCmap hout t ht ht1 k hk rfl rfl epsilon hsmall
  have hU2 := (parameterRound2_paperAtlasCj_mono_order (show 2 ≤ k/2 by omega)
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).trans hUbudget
  have hUfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU2
  have hUreal : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
      (epsilon/8)*t := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU2
    have hb : 0 ≤ (epsilon/8)*t := by positivity
    simpa only [ENNReal.toReal_ofReal hb] using h
  let f := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
    (fun z => state.map z-packet.referenceMap z)
  let u := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB _ (state.smooth.sub packet.referenceMap_smooth)
  have hu := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB U hU
  have hsum := parameterRound2_paperAtlasCj_add_le 2 f u O packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    (fun _ _ hy => hy.1) hf hu state.mapDistance_finite hUfinite
  have heq : (fun i x => f i x+u i x) =
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => state.map z+U z-packet.referenceMap z) := by
    funext i x r
    simp only [f,u,incrementsOriginalMapCoordinates,map_add,map_sub,Pi.add_apply,Pi.sub_apply]
    ring
  rw [heq] at hsum
  have hReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨state.mapDistance_finite,hUfinite⟩) hsum
  rw [ENNReal.toReal_add state.mapDistance_finite hUfinite] at hReal
  have hRatio := iterationScale_initial_ratio_le_half ht htsmall
  have hRate := (repair_step_scale_ratios ht).1
  have htau : t^(6/5 : ℝ) ≤ t/2 := by
    have hr : t^(6/5 : ℝ)/t ≤ 1/2 := hRate.trans_le hRatio
    exact (div_le_iff₀ ht).mp hr |>.trans_eq (by ring)
  have hMul := mul_le_mul_of_nonneg_left htau (div_nonneg heps (by norm_num : (0:ℝ) ≤ 4))
  change (packet.mapDistance (fun z => state.map z+U z)).toReal ≤ _ at hReal ⊢
  nlinarith only [hReal,state.map_close,hUreal,hMul]

/-- Fixed reference contribution to the low-order pair entrance. -/
def round3RepairReferenceLowBase : ℝ :=
  (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+
  (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal

/-- The low-order baseline in the actual pair recurrence is paid by fixed
reference data and the invariant C2 radius, independently of the current map. -/
theorem round3_repair_state_low_pair_base
    {budget epsilon eta t : ℝ} {k : ℕ}
    (state : Round3RepairClosedState packet budget epsilon eta k t)
    (ht : 0 ≤ t) (heps : 0 ≤ epsilon)
    (hFixed : round3RepairReferenceLowBase packet+epsilon/4 ≤ budget/4) :
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart state.map)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤ budget/4 := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  let ref := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap
  let f := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
    (fun z => state.map z-packet.referenceMap z)
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  have href := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB _ (state.smooth.sub packet.referenceMap_smooth)
  have hrfin := parameterRound2_paperAtlasCj_finite_of_compact ref O packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    packet.closedSamples_compact (fun _ _ hy => hy.1) href 2
  have hadd := parameterRound2_paperAtlasCj_add_le 2 ref f O packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    (fun _ _ hy => hy.1) href hf hrfin state.mapDistance_finite
  have heq : (fun i x => ref i x+f i x) =
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart state.map := by
    funext i x r
    simp only [ref,f,incrementsOriginalMapCoordinates,map_add,map_sub,Pi.add_apply,Pi.sub_apply]
    ring
  rw [heq] at hadd
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hrfin,state.mapDistance_finite⟩) hadd
  rw [ENNReal.toReal_add hrfin state.mapDistance_finite] at hreal
  have hclose : (packet.mapDistance state.map).toReal ≤ epsilon/4 := by
    exact state.map_close.trans (by nlinarith [mul_nonneg heps ht])
  dsimp only [round3RepairReferenceLowBase] at hFixed
  change _ ≤ _+(packet.mapDistance state.map).toReal at hreal
  linarith only [hreal,hclose,hFixed]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_same_increment_reference_envelope

#print axioms GlobalEmbedding.Continuation.round3_repair_state_low_pair_base
