import Smoothing.Round3RepairClosedSeries

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
local instance round3RepairClosedTensorChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairClosedTensorIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- The true normalized tensor has a uniform original C0 bound, extracted
from the actual current pair budget with no toReal infinity shortcut. -/
theorem round3_repair_state_normalized_defect_C0
    {budget epsilon eta t : ℝ} {k : ℕ}
    (state : Round3RepairClosedState packet budget epsilon eta k t) :
    paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
      (packet.normalizedDefect state.map k t))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal budget := by
  let H := incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
    (packet.normalizedDefect state.map k t)
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  have hzero : paperAtlasCj 0 H O packet.closedSamples ≤ paperAtlasWeighted 0 (40*(k+1)) t H O packet.closedSamples := by
    unfold paperAtlasWeighted
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (40*(k+1)+1)) =>
      show (0:ℝ≥0∞) ≤ ENNReal.ofReal t^j*paperAtlasCj (j+0) H O packet.closedSamples from zero_le)
      (show 0 ∈ Finset.range (40*(k+1)+1) by simp)
    simpa only [pow_zero,zero_add,one_mul] using h
  have hpair : paperAtlasCj 0 H O packet.closedSamples ≤ packet.pairNorm state.map k t (40*(k+1)) :=
    hzero.trans (le_add_left le_rfl)
  have hbound : paperAtlasCj 0 H O packet.closedSamples ≤
      ENNReal.ofReal (packet.pairNorm state.map k t (40*(k+1))).toReal := by
    rw [ENNReal.ofReal_toReal (state.pairNorm_finite (40*(k+1)))]
    exact hpair
  exact hbound.trans (ENNReal.ofReal_le_ofReal state.pair_budget)

/-- Every original ordered tensor coefficient of the actual normalized
defect is uniformly bounded at every real sample. -/
theorem round3_repair_state_normalized_defect_at_sample
    {budget epsilon eta t : ℝ} {k : ℕ}
    (state : Round3RepairClosedState packet budget epsilon eta k t)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Fin (n+d) → ℝ)
    (hy : y ∈ packet.closedSamples i) :
    ‖incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
      (packet.normalizedDefect state.map k t) i y‖ ≤ budget := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hH := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB state.map state.smooth packet.metric packet.metric_smooth (t^k)
  have hbound := (le_iSup (fun i => paperCoordinateCj 0
    (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart (packet.normalizedDefect state.map k t) i)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) i).trans
      (round3_repair_state_normalized_defect_C0 packet state)
  have hbudget : 0 ≤ budget := ENNReal.toReal_nonneg.trans state.pair_budget
  have h := iteratedFDeriv_le_of_paperCoordinateCj_le
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
    (fun _ hx => hx.1) (hH i) hbudget hbound (show 0 ≤ (0:ℕ) from le_rfl) hy
  unfold Round3RepairFixedSmoothingPacket.normalizedDefect
  simpa only [norm_iteratedFDeriv_zero,pow_zero,one_mul] using h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_state_normalized_defect_C0
#print axioms GlobalEmbedding.Continuation.round3_repair_state_normalized_defect_at_sample
