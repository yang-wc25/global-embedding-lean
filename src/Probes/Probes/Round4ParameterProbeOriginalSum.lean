import Smoothing.Round3RepairOriginalSumBound
import GlobalEmbedding.Offline.ProbeTailEstimates

/-! Fixed-order summation on the actual closed convolution domains.
The original growing-order bounds provide joint smoothness and convergence;
a sharper independent majorant controls the very same sum in the original
atlas maximum. No sampling set is replaced by an entire chart target. -/
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
local instance round4ParameterProbeOriginalSumChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterProbeOriginalSumIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)


/-- The actual original closed-domain MAX norm passes to the same
physical sum with factor one at any already-controlled derivative order. -/
theorem round4ParameterProbe_closed_original_sum_fixed_order
    (hK : Data.parameterSet = univ)
    (u : ℕ → P × M → Ey) (stage : ℕ → ℕ)
    (hu : ∀ j, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (u j))
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 4 ≤ stage j)
    (a : ℕ)
    (t C : ℝ) (ht : 0 < t) (htsmall : t ≤ (1/2 : ℝ)^5) (hC : 0 < C)
    (hbound : ∀ j, paperAtlasCj (stage j/2)
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u j))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (C*iterationScale t j))
    (D p : ℝ) (hD : 0 ≤ D) (hp : 0 < p)
    (horder : ∀ j, paperAtlasCj a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u j))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (D*iterationScale t j^p)) :
    paperAtlasCj a (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal (D*∑' j, iterationScale t j^p) := by
  have ht1 : t < 1 := by norm_num at htsmall; linarith
  have hs := round3_repair_closed_original_series packet hK u stage hu hstage hmin t C ht htsmall hC hbound
  have hPartial (J : ℕ) : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞
      (fun z => ∑ j ∈ Finset.range J, u j z) := ContMDiff.sum fun j _ => hu j
  have hJet := hs.2.2.1
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  let f := fun j => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u j)
  have hf (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      ContDiffOn ℝ ∞ (f j i) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) :=
    parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB (u j) (hu j) i
  have hG (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB (fun z => ∑' j, u j z) hs.2.1 i
  have hfinite (J : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => ∑ j ∈ Finset.range J, u j z) i = (fun y => ∑ j ∈ Finset.range J, f j i y) := by
    funext y
    simp only [f,incrementsOriginalMapCoordinates,map_sum]
  have hb0 (j : ℕ) : 0 ≤ D*iterationScale t j^p :=
    mul_nonneg hD (Real.rpow_nonneg (iterationScale_pos ht j).le _)
  have hsmall (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      paperCoordinateCj a (f j i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i) ≤
      ENNReal.ofReal (D*iterationScale t j^p) :=
    (le_iSup (fun b => paperCoordinateCj a (f j b)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart b) (packet.closedSamples b)) i).trans (horder j)
  have hBudget : Tendsto (fun J => ∑ j ∈ Finset.range J, D*iterationScale t j^p) atTop
      (𝓝 (D*∑' j, iterationScale t j^p)) := by
    simpa only [tsum_mul_left] using ((summable_iterationScale_power ht ht1 hp).mul_left D).hasSum.tendsto_sum_nat
  have hFinal : paperAtlasCj a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (D*∑' j, iterationScale t j^p) := by
    apply iSup_le
    intro i
    apply paperCoordinateCj_le_of_jet_tendsto a
      (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
      (fun _ hy => hy.1)
      (fun J => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => ∑ j ∈ Finset.range J, u j z) i)
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z) i)
      (fun J => parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
        packet.domain.atlas_smooth hB _ (hPartial J) i) (hG i)
      (fun J => ∑ j ∈ Finset.range J, D*iterationScale t j^p)
      (fun J => Finset.sum_nonneg fun j _ => hb0 j) hBudget
    · intro J
      rw [hfinite J i]
      exact paperCoordinateCj_sum_le a
        (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
        (fun _ hy => hy.1) (Finset.range J) (fun j => f j i) (fun j _ => hf j i)
        (fun j => D*iterationScale t j^p) (fun j _ => hb0 j) (fun j _ => hsmall j i)
    · intro a _ y hy
      exact hJet i a y hy.1
  exact hFinal

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_closed_original_sum_fixed_order
