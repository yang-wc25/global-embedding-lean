import NormalPolar.ActualRepairModelFirstDefectClosedState
import NormalPolar.ActualRepairModelFirstDefectStateCap

/-! Fixed-reference finite jets choose the actual first-state scale before
any candidate U0. At every smaller original scale, the produced component
bounds pay all closed-state fields. This theorem is a consumer on a genuine
parameter manifold P; a chartwise raw producer on that same P is still needed
for an unconditional construction. In particular no Euclidean full-domain
compact packet is inferred from the native raw theorems. -/

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
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

theorem actualRepairModelFirstDefect_exists_closed_state_scale
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hK : Data.parameterSet = univ) (hmetric : packet.metric = Data.H)
    (CU CE budget epsilon eta cap : ℝ) (hCU : 0 ≤ CU)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hcap : 0 < cap)
    (hbudget : 4 *
      ((paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal) < budget) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ cap ∧ ∀ t : ℝ, 0 < t → t ≤ t0 →
      ∀ (U : P × M → Ey)
      (hcoord : ∀ i, ∃ G : Set (Fin (n+d) → ℝ), IsOpen G ∧ packet.closedSamples i ⊆ G ∧
        G ⊆ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i ∧
        ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U i) G)
      (hU2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
          CU*t^(10 : ℕ)/t^((6 : ℝ)/5))
      (hUW : (paperAtlasWeighted 2 440 (t^((6 : ℝ)/5)) (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
          CU*t^(10 : ℕ)/t^((6 : ℝ)/5))
      (W : Set (P × M))
      (error : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples W)
      (hvalue : error.val = fun p x => packet.normalizedDefect
        (actualRepairModelFirstDefectFirstMap packet.referenceMap U (t^10)) 10 (t^((6 : ℝ)/5)) p x-Data.H p x)
      (herror : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart
        packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) (t^((6 : ℝ)/5)) 440 error ≤
          CE*(t^(30 : ℝ)+t^((24 : ℝ)/5))),
      ∃ initial : Round3RepairClosedState packet budget epsilon eta 10 (t^((6 : ℝ)/5)),
        initial.map = actualRepairModelFirstDefectFirstMap packet.referenceMap U (t^10) := by
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  let S := packet.closedSamples
  let f := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap
  let g := incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H
  let Cref := (paperAtlasCj 2 f O S).toReal
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hO := parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i) := by
    intro i
    change ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H i) _
    rw [← hmetric]
    exact packet.metric_smooth i
  have hf442 := parameterRound2_paperAtlasCj_finite_of_compact f O S hO packet.closedSamples_compact hSO hf 442
  have hg440 := parameterRound2_paperAtlasCj_finite_of_compact g O S hO packet.closedSamples_compact hSO hg 440
  obtain ⟨refcap,hrefcap,hrefcap1,hrefcapCap,href⟩ :=
    parameterRound2_exists_reference_pair_scale 440 f g O S hf442 hg440 budget cap hcap hbudget
  have hbudget0 : 0 < budget := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) hbudget
  have hs := actualRepairModelFirstDefect_state_cap Cref CU CE budget epsilon eta refcap
    ENNReal.toReal_nonneg hCU hbudget0 hepsilon heta hrefcap
  let t0 := actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta refcap
  refine ⟨t0,hs.1,hs.2.1.trans hrefcapCap,?_⟩
  intro t ht htt U hcoord hU2 hUW W error hvalue herror
  obtain ⟨htauHalf,hMapPaid,hIncPaid,hErrorEta,hErrorBudget⟩ := hs.2.2.2 t ht htt
  have ht1 : t ≤ 1 := (htt.trans hs.2.2.1).trans (by norm_num)
  have htau : 0 < t^((6 : ℝ)/5) := Real.rpow_pos_of_pos ht _
  have htauT : t^((6 : ℝ)/5) ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num : (1 : ℝ) ≤ 6/5)
  have hRef := href (t^((6 : ℝ)/5)) htau.le (htauT.trans (htt.trans hs.2.1))
  let initial := actualRepairModelFirstDefectClosedState packet hK hmetric U (t^10) (t^((6 : ℝ)/5))
    budget epsilon eta (CU*t^10/t^((6 : ℝ)/5)) (CU*t^10/t^((6 : ℝ)/5)) (CE*(t^(30 : ℝ)+t^((24 : ℝ)/5)))
    hcoord hU2 hUW W error hvalue herror hMapPaid (hErrorEta.trans (by linarith))
    (by change _ ≤ _ at hRef; linarith)
  exact ⟨initial,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_exists_closed_state_scale
