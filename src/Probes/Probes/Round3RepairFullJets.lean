import Probes.Round3RepairFullLimit

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
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
local instance round3RepairFullJetsChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairFullJetsIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)












namespace Round3RepairInfiniteBlocks
variable [CompactSpace M]
  {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
  (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta t ht ht1 initial)

/-- The actual finite state at every natural time is the partial sum of the
same literal oscillatory increments used for the infinite limit. -/
theorem actual_partial_sum (j : ℕ) :
    (run.state packet j).map = fun z => initial.map z+∑ a ∈ Finset.range j, run.increment packet a z := by
  induction j with
  | zero => simpa using run.initial_state_map packet
  | succ j ih =>
    rw [run.actual_update packet j,ih]
    funext z
    simp only [Finset.sum_range_succ]
    abel

/-- Every original mixed coordinate jet of the true full-time repair states
converges to the corresponding jet of the same physical metric limit.  This
includes all original differentiation-domain points, not only the interior
convolution buffers. -/
theorem full_original_derivative_convergence
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    ∀ i a y, y ∈ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i →
      Tendsto (fun J => iteratedFDeriv ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (run.state packet J).map i) y)
        atTop (𝓝 (iteratedFDeriv ℝ a
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart Fstar i) y)) := by
  intro Fstar i a y hy
  have htSmall : t ≤ (1/2 : ℝ)^5 := by
    have h := (run.entry 0).admissible.trans (hSmall 0)
    simpa only [run.initial_index,iterationScale_zero] using h
  have hActual := run.full_increment_control packet heps hDisp hTheta
  have hs := round3_repair_closed_original_series packet hK (run.increment packet) (run.stage packet)
    (fun j => (hActual j).1) (run.full_stage_tendsto packet)
    (fun j => (show 4 ≤ 10 by norm_num).trans (run.full_stage_ge_ten packet j))
    t (epsilon/8) ht htSmall (by positivity) (fun j => (hActual j).2)
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hOpen := parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i
  have hG0 := (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB initial.map initial.smooth i).contDiffAt (hOpen.mem_nhds hy)
  have hU (J : ℕ) := (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB (fun z => ∑ j ∈ Finset.range J, run.increment packet j z)
    (ContMDiff.sum fun j _ => (hActual j).1) i).contDiffAt (hOpen.mem_nhds hy)
  have hSum := (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB (fun z => ∑' j, run.increment packet j z) hs.2.1 i).contDiffAt (hOpen.mem_nhds hy)
  have hAddCoords (f g : P × M → Ey) :
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => f z+g z) i =
      fun y => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart f i y+
        incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart g i y := by
    funext y
    simp only [incrementsOriginalMapCoordinates,map_add]
  have hConst : Tendsto (fun _ : ℕ => iteratedFDeriv ℝ a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart initial.map i) y) atTop
      (𝓝 (iteratedFDeriv ℝ a
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart initial.map i) y)) :=
    tendsto_const_nhds
  have hLimit := hConst.add (hs.2.2.1 i a y hy)
  convert hLimit using 1
  · funext J
    rw [run.actual_partial_sum packet J,hAddCoords]
    exact fun_iteratedFDeriv_add_apply (hG0.of_le (by simp)) ((hU J).of_le (by simp))
  · change 𝓝 (iteratedFDeriv ℝ a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => initial.map z+∑' j, run.increment packet j z) i) y) = _
    rw [hAddCoords]
    congr 1
    exact fun_iteratedFDeriv_add_apply (hG0.of_le (by simp)) (hSum.of_le (by simp))

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actual_partial_sum
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.full_original_derivative_convergence
