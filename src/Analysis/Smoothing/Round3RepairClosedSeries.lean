import Smoothing.Round3RepairClosedBuffers
import GlobalEmbedding.Offline.RepairSeriesLimit

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
local instance round3RepairClosedSeriesChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairClosedSeriesIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- The actual original MAX estimates on the closed Ω/Q domain give one
jointly smooth physical sum, all its original coordinate derivative limits,
and a strict C2 MAX reserve on the fixed covering open buffers. -/
theorem round3_repair_closed_actual_series
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
    (∀ i a, (∀ y ∈ packet.closedBuffer i,
      iteratedFDerivWithin ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z) i)
        (packet.closedBuffer i) y =
      ∑' j, iteratedFDerivWithin ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u j) i) (packet.closedBuffer i) y) ∧
      TendstoUniformlyOn
        (fun J => iteratedFDerivWithin ℝ a
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑ j ∈ Finset.range J, u j z) i)
          (packet.closedBuffer i))
        (iteratedFDerivWithin ℝ a
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z) i)
          (packet.closedBuffer i)) atTop (packet.closedBuffer i)) ∧
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z))
      packet.closedBuffer packet.closedBuffer < ENNReal.ofReal C := by
  have ht1 : t < 1 := by norm_num at htsmall; linarith
  let f := fun j => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u j)
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hf (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      ContDiffOn ℝ ∞ (f j i) (packet.closedBuffer i) :=
    (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB (u j) (hu j) i).mono
        (fun _ hy => (packet.closedBuffer_subset_samples i hy).1)
  have hb (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      paperCoordinateCj (stage j/2) (f j i) (packet.closedBuffer i) (packet.closedBuffer i) ≤
        ENNReal.ofReal (C*iterationScale t j) :=
    (packet.closedBuffer_map_bound (u j) (hu j) (stage j/2) i).trans (hbound j)
  have hs (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    smooth_series_on_of_paper_stage_bound (packet.closedBuffer_open i) (fun j => f j i) stage
      (fun j => hf j i) hstage ht ht1 hC.le (fun j => hb j i)
  have hsum : incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => ∑' j, u j z) =
      (fun i y => ∑' j, f j i y) := by
    funext i y
    exact (EuclideanSpace.equiv (Fin N) ℝ).map_tsum
  have hfinite (J : ℕ) :
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => ∑ j ∈ Finset.range J, u j z) = (fun i y => ∑ j ∈ Finset.range J, f j i y) := by
    funext i y
    simp only [f,incrementsOriginalMapCoordinates,map_sum]
  have hSummable (z : P × M) : Summable (fun j => u j z) := by
    obtain ⟨i,hp,hx,hz⟩ := packet.closedBuffer_cover hK z
    let y := parameterRound2_originalForwardCoordinates Data i z
    have hVal (j : ℕ) : ‖f j i y‖ ≤ C*iterationScale t j := by
      have h := iteratedFDeriv_le_of_paperCoordinateCj_le (packet.closedBuffer_open i) (Subset.refl _)
        (hf j i) (mul_nonneg hC.le (iterationScale_pos ht j).le) (hb j i) (Nat.zero_le (stage j/2)) hz
      simpa only [norm_iteratedFDeriv_zero,pow_zero,one_mul] using h
    have hPi : Summable (fun j => f j i y) := ((summable_iterationScale ht ht1).mul_left C).of_norm_bounded hVal
    have hNative := (EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap.summable hPi
    have he := parameterRound2_originalForward_left_inv Data i z hp hx
    have hPoint : incrementsOriginalJointPoint Data.atlas packet.parameterFamily.chart i y = z := by
      rw [packet.chart_eq]
      exact he
    simpa only [f,incrementsOriginalMapCoordinates,hPoint,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hNative
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (fun z => ∑' j, u j z) := by
    rw [modelWithCornersSelf_prod]
    intro z
    obtain ⟨i,hp,hx,hz⟩ := packet.closedBuffer_cover hK z
    have hcoords := (hs i).1
    have hsum_i := congrFun hsum i
    rw [← hsum_i,packet.chart_eq] at hcoords
    exact round3_repair_original_map_contMDiffAt_of_coordinate_germ Data packet.domain _ i
      (packet.closedBuffer i) (packet.closedBuffer_open i) hcoords z hp hx hz
  refine ⟨hSummable,hSmooth,?_,?_⟩
  · intro i a
    rw [hsum]
    simp_rw [hfinite]
    exact ⟨fun y hy => (hs i).2.1 a y hy,(hs i).2.2 a⟩
  · rw [hsum]
    exact (paperAtlasCj_tsum_lt_of_stage_bound 2 packet.closedBuffer packet.closedBuffer_open f stage hf
      hstage (fun j => by have := hmin j; omega) ht htsmall hC
      (fun j => iSup_le fun i => hb j i)).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_closed_actual_series
