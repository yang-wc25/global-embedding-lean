import Smoothing.Round3RepairClosedTensorBound
import Smoothing.Round3RepairMetricCoordinates
import GlobalEmbedding.Offline.RepairSequenceScales
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
local instance round3RepairBlockMetricChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairBlockMetricIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- Actual block endpoints have the metric of their one physical series.
All normalized-defect bounds and all derivative convergence are derived from
the same original state/increment norms.  They are not terminal hypotheses. -/
theorem round3_repair_block_endpoints_metric_limit
    (hK : Data.parameterSet = univ)
    (budget epsilon eta t C : ℝ) (ht : 0 < t) (htsmall : t ≤ (1/2 : ℝ)^5) (hC : 0 < C)
    (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop) (hmin : ∀ j, 10 ≤ stage j)
    (time : ℕ → ℝ) (hTimePos : ∀ j, 0 < time j)
    (hTimeBound : ∀ j, time j ≤ iterationScale t j)
    (states : ∀ j, Round3RepairClosedState packet budget epsilon eta (stage j) (time j))
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
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples < ENNReal.ofReal C := by
  intro Fstar
  have ht1 : t < 1 := by norm_num at htsmall; linarith
  have hs := round3_repair_closed_actual_series packet hK u stage hu hstage
    (fun j => (show 4 ≤ 10 by norm_num).trans (hmin j)) t C ht htsmall hC hbound
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hStar : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ Fstar := (states 0).smooth.add hs.2.1
  have hTel : ∀ j, (states j).map = fun z => (states 0).map z+∑ i ∈ Finset.range j, u i z := by
    intro j
    induction j with
    | zero => funext z; simp
    | succ j ih =>
      rw [hUpdate j,ih]
      funext z
      simp only [Finset.sum_range_succ]
      abel
  have hAddCoords (f g : P × M → Ey) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => f z+g z) i =
      fun y => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart f i y+
        incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart g i y := by
    funext y
    simp only [incrementsOriginalMapCoordinates,map_add]
  have hdelta : Tendsto (fun j => time j ^ stage j) atTop (𝓝 (0:ℝ)) :=
by
    have hDom (j : ℕ) : time j ^ stage j ≤ iterationScale t j := by
      have hOne : time j ≤ 1 := (hTimeBound j).trans (iterationScale_lt_one ht.le ht1 j).le
      have h := pow_le_pow_of_le_one (hTimePos j).le hOne (show 1 ≤ stage j by have := hmin j; omega)
      exact (by simpa only [pow_one] using h : time j ^ stage j ≤ time j).trans (hTimeBound j)
    exact ((summable_iterationScale ht ht1).of_nonneg_of_le
      (fun j => pow_nonneg (hTimePos j).le _) hDom).tendsto_atTop_zero
  refine ⟨hs.1,hStar,?_,?_⟩
  · intro p
    funext x
    let z : P × M := (p,x)
    obtain ⟨i,hp,hx,hy⟩ := packet.closedBuffer_cover hK z
    let y := parameterRound2_originalForwardCoordinates Data i z
    have hyS : y ∈ packet.closedSamples i := packet.closedBuffer_subset_samples i hy
    have hyO : y ∈ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i := hyS.1
    have hOpen := packet.closedBuffer_open i
    have hG0 := (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB (states 0).map (states 0).smooth i).contDiffAt
        ((parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i).mem_nhds hyO)
    have hU (j : ℕ) := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB (fun z => ∑ a ∈ Finset.range j, u a z)
      (ContMDiff.sum fun a _ => hu a) i
    have hSum := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB (fun z => ∑' j, u j z) hs.2.1 i
    have hDWithin := (tendstoUniformlyOn_fderivWithin_of_iterated_one hOpen.uniqueDiffOn
      ((hs.2.2.1 i 1).2)).tendsto_at hy
    have hDPartial : Tendsto
        (fun j => fderiv ℝ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
          (fun z => ∑ a ∈ Finset.range j, u a z) i) y) atTop
        (𝓝 (fderiv ℝ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
          (fun z => ∑' j, u j z) i) y)) := by
      simpa only [fderivWithin_of_isOpen hOpen hy] using hDWithin
    have hD : Tendsto
        (fun j => fderiv ℝ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (states j).map i) y) atTop
        (𝓝 (fderiv ℝ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart Fstar i) y)) := by
      have hConst : Tendsto (fun _ : ℕ => fderiv ℝ
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (states 0).map i) y) atTop
          (𝓝 (fderiv ℝ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (states 0).map i) y)) := tendsto_const_nhds
      have h := hConst.add hDPartial
      convert h using 1
      · funext j
        rw [hTel j,hAddCoords]
        exact fderiv_add (hG0.differentiableAt (by simp))
          (((hU j).contDiffAt ((parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i).mem_nhds hyO)).differentiableAt (by simp))
      · change 𝓝 (fderiv ℝ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
          (fun z => (states 0).map z+∑' j, u j z) i) y) = _
        rw [hAddCoords]
        congr 1
        exact fderiv_add (hG0.differentiableAt (by simp))
          ((hSum.contDiffAt ((parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i).mem_nhds hyO)).differentiableAt (by simp))
    have hCoeff :
        incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
          (fun p x => inducedMetric (I := IT) (fun z => Fstar (p,z)) x) i y =
        incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart packet.metric i y := by
      funext a
      have hMetric := round3_repair_metric_coordinates_tendsto Data.atlas packet.parameterFamily.chart
        packet.domain.atlas_smooth hB (fun j => (states j).map) Fstar (fun j => (states j).smooth) hStar i y hyO hD a
      have hNorm : IsBoundedUnder (· ≤ ·) atTop (fun j =>
          ‖incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
            (packet.normalizedDefect (states j).map (stage j) (time j)) i y a‖) := by
        refine ⟨budget,?_⟩
        change ∀ᶠ j : ℕ in atTop, ‖incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
          (packet.normalizedDefect (states j).map (stage j) (time j)) i y a‖ ≤ budget
        exact Eventually.of_forall fun j =>
          (norm_le_pi_norm _ a).trans (round3_repair_state_normalized_defect_at_sample packet (states j) i y hyS)
      have hdelta2 : Tendsto (fun j => (time j ^ stage j)^2) atTop (𝓝 (0:ℝ)) := by
        simpa using hdelta.pow 2
      have hProduct : Tendsto (fun j => (time j ^ stage j)^2*
          incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
            (packet.normalizedDefect (states j).map (stage j) (time j)) i y a) atTop (𝓝 0) := by
        simpa only [Pi.smul_apply,smul_eq_mul,Pi.mul_def] using
          NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hdelta2 hNorm
      have hDefect (j : ℕ) :
          incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart packet.metric i y a-
          incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
            (fun p x => inducedMetric (I := IT) (fun z => (states j).map (p,z)) x) i y a =
          (time j ^ stage j)^2*
          incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
            (packet.normalizedDefect (states j).map (stage j) (time j)) i y a := by
        have hNZ : (time j ^ stage j)^2 ≠ 0 := pow_ne_zero _ ((pow_pos (hTimePos j) _).ne')
        simp only [incrementsOriginalTensorCoordinates,Round3RepairFixedSmoothingPacket.normalizedDefect,
          LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
        rw [← mul_assoc,mul_inv_cancel₀ hNZ,one_mul]
      have hZero : Tendsto (fun j =>
          incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart packet.metric i y a-
          incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
            (fun p x => inducedMetric (I := IT) (fun z => (states j).map (p,z)) x) i y a) atTop (𝓝 0) := by
        simpa only [hDefect] using hProduct
      have hEq := tendsto_nhds_unique (tendsto_const_nhds.sub hMetric) hZero
      exact (sub_eq_zero.mp hEq).symm
    have hNative := congrArg (tensorFromFrameComponents
      (bufferedSourceChartBasis Data.atlas packet.domain.atlas_smooth i.1 (incrementsOriginalSourcePoint y) hyO.1)) hCoeff
    rw [reconstruct_incrementsOriginalTensorCoordinates Data.atlas packet.domain.atlas_smooth packet.parameterFamily.chart _ i y hyO,
      reconstruct_incrementsOriginalTensorCoordinates Data.atlas packet.domain.atlas_smooth packet.parameterFamily.chart _ i y hyO] at hNative
    have hPoint : incrementsOriginalJointPoint Data.atlas packet.parameterFamily.chart i y = z := by
      rw [packet.chart_eq]
      exact parameterRound2_originalForward_left_inv Data i z hp hx
    change inducedMetric (I := IT) (fun w => Fstar (z.1,w)) z.2 = packet.metric z.1 z.2
    rw [← hPoint]
    exact hNative
  · have heq : (fun z => Fstar z-(states 0).map z) = (fun z => ∑' j, u j z) := by
      funext z
      exact add_sub_cancel_left _ _
    rw [heq]
    exact (round3_repair_closed_original_series packet hK u stage hu hstage
      (fun j => (show 4 ≤ 10 by norm_num).trans (hmin j)) t C ht htsmall hC hbound).2.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_block_endpoints_metric_limit
