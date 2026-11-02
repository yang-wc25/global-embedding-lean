import Smoothing.Round3RepairClosedMetricLimit
import Smoothing.Round3RepairOriginalSeries

/-! The fixed convolution sampling domains contain actual open buffers.
On the whole physical parameter manifold they cover every point, using the
actual parameter plateau and the original source atlas.  No compact sampling
domain is identified with an entire chart target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
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
local instance round3RepairOriginalMetricChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairOriginalMetricIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)


/-- Metric equality and the strict ORIGINAL C2 reference reserve belong to
one and the same physical limit.  All C2 finite/limit facts are proved from
the actual summable increment bounds on the same closed Ω/Q samples. -/
theorem round3_repair_closed_original_metric_limit
    (hK : Data.parameterSet = univ)
    (budget epsilon eta t C : ℝ) (heps : 0 < epsilon)
    (ht : 0 < t) (htsmall : t ≤ (1/2 : ℝ)^5) (hC : 0 < C)
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 10 ≤ stage j)
    (states : ∀ j, Round3RepairClosedState packet budget epsilon eta (stage j) (iterationScale t j))
    (u : ℕ → P × M → Ey)
    (hu : ∀ j, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (u j))
    (hUpdate : ∀ j, (states (j+1)).map = fun z => (states j).map z+u j z)
    (hbound : ∀ j, paperAtlasCj (stage j/2)
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u j))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (C*iterationScale t j)) :
    let Fstar := fun z => (states 0).map z+∑' j, u j z
    (∀ z, Summable (fun j => u j z)) ∧
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ Fstar ∧
    (∀ p, inducedMetric (I := IT) (fun x => Fstar (p,x)) = packet.metric p) ∧
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => Fstar z-(states 0).map z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples < ENNReal.ofReal C ∧
    packet.mapDistance Fstar ≠ ⊤ ∧ (packet.mapDistance Fstar).toReal < epsilon/4+C := by
  intro Fstar
  have hMetric := round3_repair_closed_states_metric_limit packet hK budget epsilon eta t C ht htsmall hC
    stage hstage hmin states u hu hUpdate hbound
  have hs := round3_repair_closed_original_series packet hK u stage hu hstage
    (fun j => (show 4 ≤ 10 by norm_num).trans (hmin j)) t C ht htsmall hC hbound
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  let f := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
    (fun z => (states 0).map z-packet.referenceMap z)
  let v := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z)
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB _ ((states 0).smooth.sub packet.referenceMap_smooth)
  have hv := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB _ hs.2.1
  have hvFin : paperAtlasCj 2 v O packet.closedSamples ≠ ⊤ :=
    ne_top_of_lt (hs.2.2.2.trans ENNReal.ofReal_lt_top)
  have hvReal : (paperAtlasCj 2 v O packet.closedSamples).toReal < C := by
    have h := (ENNReal.toReal_lt_toReal hvFin ENNReal.ofReal_ne_top).mpr hs.2.2.2
    simpa only [ENNReal.toReal_ofReal hC.le] using h
  have hadd := parameterRound2_paperAtlasCj_add_le 2 f v O packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    (fun _ _ hy => hy.1) hf hv (states 0).mapDistance_finite hvFin
  have heq : (fun i x => f i x+v i x) =
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => Fstar z-packet.referenceMap z) := by
    funext i x r
    simp only [f,v,Fstar,incrementsOriginalMapCoordinates,map_add,map_sub,Pi.add_apply,Pi.sub_apply]
    ring
  rw [heq] at hadd
  have hfin : packet.mapDistance Fstar ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨(states 0).mapDistance_finite,hvFin⟩) hadd
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(states 0).mapDistance_finite,hvFin⟩) hadd
  rw [ENNReal.toReal_add (states 0).mapDistance_finite hvFin] at hreal
  have hOld : (packet.mapDistance (states 0).map).toReal ≤ epsilon/4 := by
    have h := (states 0).map_close
    have ht0 : 0 ≤ iterationScale t 0 := (iterationScale_pos ht 0).le
    nlinarith [mul_nonneg heps.le ht0]
  have hDiff : (fun z => Fstar z-(states 0).map z) = (fun z => ∑' j, u j z) := by
    funext z
    exact add_sub_cancel_left _ _
  refine ⟨hMetric.1,hMetric.2.1,hMetric.2.2.1,?_,hfin,?_⟩
  · rw [hDiff]
    exact hs.2.2.2
  · change (packet.mapDistance Fstar).toReal ≤ (packet.mapDistance (states 0).map).toReal+
      (paperAtlasCj 2 v O packet.closedSamples).toReal at hreal
    linarith only [hreal,hOld,hvReal]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_closed_original_metric_limit
