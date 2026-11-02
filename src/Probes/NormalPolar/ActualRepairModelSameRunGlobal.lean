import NormalPolar.ActualRepairModelSliceNorm
import NormalPolar.ActualRepairModelModuli

/-!
# Whole-source probe budgets of the same actual repair trajectory

The one actual infinite sum is pulled back through the original parameter
chart. Its smoothness, exact metric, spatial tails, and native response tails
are all consequences of that same run. Sampling-atlas support coverage is
provided by the existing packet, not added as a conclusion assumption.
-/

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
local instance actualRepairModelSameRunGlobalChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairModelSameRunGlobalIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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


open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

/-- One literal repaired family, with the source unchanged and only the
original actual parameter chart pulled back to its Pi coordinates. -/
def actualRepairModelFamily (b : Fin Data.parameterCount) (u : Fin d → ℝ) (x : M) : Ey :=
  actualRepairModelChartFamily (packet.parameterFamily.chart b)
    (fun z => initial.map z + ∑' j, run.increment packet j z) u x

theorem actualRepairModelFamily_smooth_metric
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (b : Fin Data.parameterCount) :
    ContMDiffOn ((𝓘(ℝ,Fin d → ℝ)).prod IT) 𝓘(ℝ,Ey) ∞
      (Function.uncurry (run.actualRepairModelFamily packet b))
      (((EuclideanSpace.equiv (Fin d) ℝ) '' (packet.parameterFamily.chart b).target) ×ˢ univ) ∧
    (∀ u, inducedMetric (I := IT) (run.actualRepairModelFamily packet b u) =
      packet.metric ((packet.parameterFamily.chart b).symm
        ((EuclideanSpace.equiv (Fin d) ℝ).symm u))) := by
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hB : packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth b
  exact ⟨actualRepairModelChartFamily_smooth _ hB _ hFull.2.1,
    fun u => hFull.2.2.1 _⟩

/-- The actual whole-source C3, C2 and C1 tails. These are derived from the
three original total-order estimates of the same trajectory, not new input
budgets for a final map. All lower derivatives in each original norm remain. -/
theorem actualRepairModelFamily_spatial_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (u : Fin d → ℝ)
    (hu : u ∈ (EuclideanSpace.equiv (Fin d) ℝ) '' packet.Q b) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let tail := run.actualRepairModelFamily packet b u -
      actualRepairModelChartFamily (packet.parameterFamily.chart b) initial.map u
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 3 tail ≤ ENNReal.ofReal (2*C*s^(228/25 : ℝ)) ∧
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (2*C*s^(264/25 : ℝ)) ∧
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (2*C*s^(12 : ℝ)) := by
  intro A tail C
  let actualTail := fun z => (initial.map z + ∑' j, run.increment packet j z)-initial.map z
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ actualTail := hFull.2.1.sub initial.smooth
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hcmp (j : ℕ) : probeAtlasCj A j tail ≤
      paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart actualTail)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples := by
    exact actualRepairModelChartFamily_spatial_le_total Data.atlas packet.domain.atlas_smooth
      packet.parameterFamily.chart hB packet.Omega packet.Q packet.source_target packet.parameter_target
      actualTail hSmooth b u hu j
  have hbound := run.probe_original_tail_84 packet hK heps hSmall hDisp hTheta hCap s hs hstart
  exact ⟨(hcmp 3).trans hbound.1,(hcmp 2).trans hbound.2.1,(hcmp 1).trans hbound.2.2⟩

/-- The Hessian, C1 and value response budgets are the actual parameter
derivatives of that SAME global correction on the complete sampling atlas.
The nonnegative moduli are defined on every real scale as the probe ABI asks. -/
theorem actualRepairModelFamily_response_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (u : Fin d → ℝ)
    (hu : u ∈ (EuclideanSpace.equiv (Fin d) ℝ) '' packet.Q b) (a : Fin d) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let tail := fun x => fderiv ℝ (fun v => run.actualRepairModelFamily packet b v x -
      actualRepairModelChartFamily (packet.parameterFamily.chart b) initial.map v x) u (Pi.single a 1)
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (s^(44/5 : ℝ)*actualRepairModelHessianModulus C s) ∧
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (s^(10 : ℝ)*actualRepairModelCOneModulus C s) ∧
    probeAtlasCj A 0 tail ≤ ENNReal.ofReal (s^(56/5 : ℝ)*actualRepairModelValueModulus C s) := by
  intro A tail C
  let actualTail := fun z => (initial.map z + ∑' j, run.increment packet j z)-initial.map z
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ actualTail := hFull.2.1.sub initial.smooth
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hcmp (j : ℕ) : probeAtlasCj A j tail ≤
      ⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) j 1
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart actualTail i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i) := by
    exact actualRepairModelChartFamily_response_le_mixed Data.atlas packet.domain.atlas_smooth
      packet.parameterFamily.chart hB packet.Omega packet.Q packet.source_target packet.parameter_target
      packet.source_sampling actualTail hSmooth b u hu a j
  have hbound := run.probe_mixed_tail_response_moduli packet hK heps hSmall hDisp hTheta hCap s hs hstart
  rcases actualRepairModel_moduli_eq_original (C := C) hs.le with ⟨hH,hC,hV⟩
  rw [hH,hC,hV]
  exact ⟨(hcmp 2).trans hbound.1,(hcmp 1).trans hbound.2.1,(hcmp 0).trans hbound.2.2⟩

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelFamily_smooth_metric
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelFamily_spatial_tails
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelFamily_response_tails

