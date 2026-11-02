import NormalPolar.ActualRepairModelFirstDefectScales
import Smoothing.Round3RepairClosedState

/-! The produced normalized-error germ fills the two tensor portions of
the original closed-state entrance. The C0 defect is a true summand of the
original weighted norm; the pair tensor is the same reference tensor plus
that same produced error. No final-state defect or pair budget is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N count : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem actualRepairModelFirstDefect_germ_C0_le
    (atlas : BufferedAtlas M Es) (param : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation atlas param i)
    (error : parameterRound2_originalTensorGermSpace atlas param S W) (j : ℕ) (tau : ℝ) :
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates atlas param error.val)
      (incrementsOriginalDifferentiation atlas param) S).toReal ≤
      parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO tau j error := by
  exact ENNReal.toReal_mono
    (parameterRound2_tensorGerm_weighted_finite atlas param S W hS hSO error 0 j tau)
    (parameterPaperAtlasCj_base_le_weighted 0 j tau _ _ _)


theorem actualRepairModelFirstDefect_real_add_bound
    (a b c : ℝ≥0∞) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (h : a ≤ b+c)
    (C : ℝ) (hC : c.toReal ≤ C) : a.toReal ≤ b.toReal+C := by
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hb,hc⟩) h).trans
    ((ENNReal.toReal_add hb hc).le.trans (add_le_add le_rfl hC))

theorem actualRepairModelFirstDefect_germ_reference_add
    (atlas : BufferedAtlas M Es) (param : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation atlas param i)
    (ref error : parameterRound2_originalTensorGermSpace atlas param S W) (j : ℕ) (tau C : ℝ)
    (hb : (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates atlas param error.val)
      (incrementsOriginalDifferentiation atlas param) S).toReal ≤ C) :
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates atlas param (ref+error).val)
      (incrementsOriginalDifferentiation atlas param) S).toReal ≤
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates atlas param ref.val)
      (incrementsOriginalDifferentiation atlas param) S).toReal+C := by
  have hs := parameterRound2_tensorGerm_weighted_add_le atlas param S W hS hSO ref error 0 j tau
  have href := parameterRound2_tensorGerm_weighted_finite atlas param S W hS hSO ref 0 j tau
  have herr := parameterRound2_tensorGerm_weighted_finite atlas param S W hS hSO error 0 j tau
  exact actualRepairModelFirstDefect_real_add_bound _ _ _ href herr hs C hb

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

theorem actualRepairModelFirstDefect_packet_tensor_bounds
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hmetric : packet.metric = Data.H) (G : P × M → Ey) (tau C : ℝ) (j : ℕ) (W : Set (P × M))
    (error : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples W)
    (hvalue : error.val = fun p x => packet.normalizedDefect G 10 tau p x-Data.H p x)
    (hbound : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart
      packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) tau j error ≤ C) :
    (packet.defectDistance G 10 tau).toReal ≤ C ∧
    (paperAtlasWeighted 0 j tau
      (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart (packet.normalizedDefect G 10 tau))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
      (paperAtlasWeighted 0 j tau
        (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart Data.H)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal+C := by
  have hRef : Data.H ∈ parameterRound2_originalTensorGermSpace
      Data.atlas packet.parameterFamily.chart packet.closedSamples W := by
    constructor
    · intro i
      refine ⟨incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i,
        parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i,
        fun _ hy => hy.1,?_⟩
      rw [← hmetric]
      exact packet.metric_smooth i
    · intro z hz
      rw [← hmetric]
      exact packet.metric_symmetric z.1 z.2
  let ref : parameterRound2_originalTensorGermSpace
      Data.atlas packet.parameterFamily.chart packet.closedSamples W := ⟨Data.H,hRef⟩
  have hsum : packet.normalizedDefect G 10 tau = (ref+error).val := by
    change packet.normalizedDefect G 10 tau = Data.H+error.val
    rw [hvalue]
    funext p x
    change packet.normalizedDefect G 10 tau p x = Data.H p x+
      (packet.normalizedDefect G 10 tau p x-Data.H p x)
    abel
  constructor
  · have hh := (actualRepairModelFirstDefect_germ_C0_le Data.atlas packet.parameterFamily.chart
        packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) error j tau).trans hbound
    rw [hvalue] at hh
    exact hh
  · rw [hsum]
    exact actualRepairModelFirstDefect_germ_reference_add Data.atlas packet.parameterFamily.chart
      packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) ref error j tau C
      ((parameterRound2_originalTensorGermSeminorm_apply Data.atlas packet.parameterFamily.chart
        packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) tau j error) ▸ hbound)

theorem actualRepairModelFirstDefect_packet_defect_at_initial_cap
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hmetric : packet.metric = Data.H) (G : P × M → Ey) (t C eta cap : ℝ)
    (ht : 0 < t) (heta : 0 < eta) (hcap : 0 < cap)
    (htcap : t ≤ actualRepairModelFirstDefectInitialCap C eta cap) (j : ℕ) (W : Set (P × M))
    (error : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples W)
    (hvalue : error.val = fun p x => packet.normalizedDefect G 10 (t^((6 : ℝ)/5)) p x-Data.H p x)
    (hbound : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart
      packet.closedSamples W packet.closedSamples_compact (fun _ _ hy => hy.1) (t^((6 : ℝ)/5)) j error ≤
        C*(t^(30 : ℝ)+t^((24 : ℝ)/5))) :
    (packet.defectDistance G 10 (t^((6 : ℝ)/5))).toReal ≤ eta/2 := by
  exact (actualRepairModelFirstDefect_packet_tensor_bounds packet hmetric G (t^((6 : ℝ)/5))
    (C*(t^(30 : ℝ)+t^((24 : ℝ)/5))) j W error hvalue hbound).1.trans
      ((actualRepairModelFirstDefect_initial_cap C eta cap heta hcap).2.2.2 t ht htcap)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_packet_tensor_bounds
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_packet_defect_at_initial_cap
