import NormalPolar.ActualRepairModelSameRunPaired
import NormalPolar.ActualRepairFinalBudgets

/-!
# Four final original probe estimates of one actual repair run

The final family, its tail and its initial model are the literal functions
from the same constructed trajectory. Only first-state estimates remain as
inputs; every final-map estimate below is proved from that trajectory.
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
variable {r : ℕ}
variable {m N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance actualRepairSameRunBudgetsChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairSameRunBudgetsIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) (Fintype.card (Fin r × Bool)) N M P}
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

/-- The complete final quantitative interface follows from the four actual
first-state estimates. No final tail, final closeness, or final parameter
budget is supplied. Constants depend on fixed costs and the fixed scale
interval, never on a later scale, source point, or probe parameter. -/
theorem actualRepairModelPairedFamily_final_budgets
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hCap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k)
    (F₀ : M → Ey) (hF₀ : ContMDiff IT 𝓘(ℝ,Ey) ∞ F₀)
    (Cmodel threshold s : ℝ) (hCmodel : 0 ≤ Cmodel)
    (hs : 0 < s) (hsT : s < threshold) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (u : ProbeParameters r) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let G := fun v : ProbeParameters r => actualRepairCenteredFamily packet.parameterFamily b p₀
      initial.map (round4PairedParameterReindex r v)
    let C := actualRepairUniformBudget Cmodel (round4ParameterProbeTailConstant cost)
      threshold (Fintype.card (Fin r × Bool))
    probeAtlasCj A 2 (G u-F₀) ≤ ENNReal.ofReal (Cmodel*s^(44/5 : ℝ)) →
    probeAtlasCj A 3 (G u) ≤ ENNReal.ofReal Cmodel →
    (∀ v, probeAtlasCj A 1 (fun x => fderiv ℝ (fun w => G w x) u v) ≤
      ENNReal.ofReal (Cmodel*s^(10 : ℕ)*‖v‖)) →
    (∀ v, probeAtlasCj A 2 (fun x => fderiv ℝ (fun w => G w x) u v) ≤
      ENNReal.ofReal (Cmodel*s^(44/5 : ℝ)*‖v‖)) →
    probeAtlasCj A 2 (run.actualRepairModelPairedFamily packet b p₀ u-F₀) ≤
      ENNReal.ofReal (C*s^(44/5 : ℝ)) ∧
    probeAtlasCj A 3 (run.actualRepairModelPairedFamily packet b p₀ u) ≤ ENNReal.ofReal C ∧
    (∀ v, probeAtlasCj A 1 (fun x => fderiv ℝ
      (fun w => run.actualRepairModelPairedFamily packet b p₀ w x) u v) ≤
      ENNReal.ofReal (C*s^(10 : ℕ)*‖v‖)) ∧
    (∀ v, probeAtlasCj A 2 (fun x => fderiv ℝ
      (fun w => run.actualRepairModelPairedFamily packet b p₀ w x) u v) ≤
      ENNReal.ofReal (C*s^(44/5 : ℝ)*‖v‖)) := by
  intro A G C hclose hthree hparamOne hparamTwo
  have hA := actualRepairSamplingAtlas_smooth Data.atlas packet.domain.atlas_smooth
    packet.Omega packet.source_target
  have hcover := actualRepairSamplingAtlas_support_cover Data.atlas packet.Omega packet.source_sampling
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hG := actualRepairModel_paired_joint_smooth
    (actualRepairParameterRadius packet.parameterFamily)
    (actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map)
    (actualRepairCenteredFamily_smooth packet.parameterFamily hB b p₀ hp₀ initial.map initial.smooth)
  have hF := (run.actualRepairModelPairedFamily_smooth_metric packet hK heps hSmall hDisp hTheta b p₀ hp₀).1
  have hspatial := run.actualRepairModelPairedFamily_spatial_tails packet hK heps hSmall hDisp hTheta
    hCap s hs hstart b p₀ hp₀ u hu
  have hdir (v : ProbeParameters r) := run.actualRepairModelPairedFamily_direction_tails packet
    hK heps hSmall hDisp hTheta hCap s hs hstart b p₀ hp₀ u hu v
  apply actual_repair_four_probe_budgets A hA hcover F₀ hF₀
    (run.actualRepairModelPairedFamily packet b p₀) G
    (actualRepairParameterRadius packet.parameterFamily) threshold Cmodel
    (round4ParameterProbeTailConstant cost) (Fintype.card (Fin r × Bool))
    hCmodel (round4ParameterProbeTailConstant_pos cost).le s hs hsT hF hG u hu
    hclose hthree hparamOne hparamTwo hspatial.2.1 hspatial.1
  · intro v
    simpa only [actualRepairModelCOneModulus_product _ s hs] using (hdir v).1
  · intro v
    simpa only [actualRepairModelHessianModulus_product _ s hs] using (hdir v).2

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelPairedFamily_final_budgets
