import Smoothing.Round3RepairOriginalJetLimit

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
local instance round3RepairOriginalSeriesChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairOriginalSeriesIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)


/-- The same actual sum has the strict C2 reserve on the ORIGINAL closed
Ω/Q samples.  The full chart transitions identify its boundary-point jets;
closed original MAX inequalities then pass to the actual limit with factor
one, not with an atlas transition loss. -/
theorem round3_repair_closed_original_series
    (hK : Data.parameterSet = univ)
    (u : ℕ → P × M → Ey) (stage : ℕ → ℕ)
    (hu : ∀ j, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (u j))
    (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 4 ≤ stage j)
    (t C : ℝ) (ht : 0 < t) (htsmall : t ≤ (1/2 : ℝ)^5) (hC : 0 < C)
    (hbound : ∀ j, paperAtlasCj (stage j/2)
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u j))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (C*iterationScale t j)) :
    (∀ z, Summable (fun j => u j z)) ∧
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (fun z => ∑' j, u j z) ∧
    (∀ i a y, y ∈ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i →
      Tendsto (fun J => iteratedFDeriv ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
          (fun z => ∑ j ∈ Finset.range J, u j z) i) y) atTop
        (𝓝 (iteratedFDeriv ℝ a
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z) i) y))) ∧
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples < ENNReal.ofReal C := by
  have ht1 : t < 1 := by norm_num at htsmall; linarith
  have hs := round3_repair_closed_actual_series packet hK u stage hu hstage hmin t C ht htsmall hC hbound
  have hPartial (J : ℕ) : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞
      (fun z => ∑ j ∈ Finset.range J, u j z) := ContMDiff.sum fun j _ => hu j
  have hJet := round3_repair_original_jets_tendsto_of_buffers packet hK
    (fun J z => ∑ j ∈ Finset.range J, u j z) (fun z => ∑' j, u j z) hPartial hs.2.1
    (fun i a y hy => ((hs.2.2.1 i a).2).tendsto_at hy)
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
  have hb0 (j : ℕ) : 0 ≤ C*iterationScale t j := mul_nonneg hC.le (iterationScale_pos ht j).le
  have hsmall (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      paperCoordinateCj 2 (f j i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i) ≤
      ENNReal.ofReal (C*iterationScale t j) :=
    (paperCoordinateCj_mono_order (by have := hmin j; omega)
      (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
      (fun _ hy => hy.1) (f j i) (hf j i)).trans
      ((le_iSup (fun b => paperCoordinateCj (stage j/2) (f j b)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart b) (packet.closedSamples b)) i).trans (hbound j))
  have hBudget : Tendsto (fun J => ∑ j ∈ Finset.range J, C*iterationScale t j) atTop
      (𝓝 (C*∑' j, iterationScale t j)) := by
    simpa only [tsum_mul_left] using ((summable_iterationScale ht ht1).mul_left C).hasSum.tendsto_sum_nat
  have hFinal : paperAtlasCj 2
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (C*∑' j, iterationScale t j) := by
    apply iSup_le
    intro i
    apply paperCoordinateCj_le_of_jet_tendsto 2
      (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
      (fun _ hy => hy.1)
      (fun J => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => ∑ j ∈ Finset.range J, u j z) i)
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z) i)
      (fun J => parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
        packet.domain.atlas_smooth hB _ (hPartial J) i) (hG i)
      (fun J => ∑ j ∈ Finset.range J, C*iterationScale t j)
      (fun J => Finset.sum_nonneg fun j _ => hb0 j) hBudget
    · intro J
      rw [hfinite J i]
      exact paperCoordinateCj_sum_le 2
        (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
        (fun _ hy => hy.1) (Finset.range J) (fun j => f j i) (fun j _ => hf j i)
        (fun j => C*iterationScale t j) (fun j _ => hb0 j) (fun j _ => hsmall j i)
    · intro a _ y hy
      exact hJet i a y hy.1
  refine ⟨hs.1,hs.2.1,hJet,hFinal.trans_lt ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff hC).mpr
  exact (mul_lt_mul_of_pos_left (tsum_iterationScale_lt_one ht htsmall) hC).trans_eq (mul_one C)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_closed_original_series
