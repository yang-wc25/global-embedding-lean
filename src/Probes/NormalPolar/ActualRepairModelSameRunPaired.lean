import NormalPolar.ActualRepairModelSameRunBall
import NormalPolar.ActualRepairModelPairedFamily

/-!
# Original paired-parameter endpoint of the actual repair tail

This is the same repaired sum, on the actual fixed centered Pi ball, with
exactly the original paired labels. No final estimate is a premise. The
actual first-state producer and raw iteration supplies remain upstream.
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
local instance actualRepairModelSameRunPairedChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairModelSameRunPairedIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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

/-- The actual sum, with the literal original paired parameters. -/
def actualRepairModelPairedFamily (b : Fin Data.parameterCount) (p₀ : P)
    (u : ProbeParameters r) (x : M) : Ey :=
  actualRepairCenteredFamily packet.parameterFamily b p₀
    (fun z => initial.map z+∑' j, run.increment packet j z)
    (round4PairedParameterReindex r u) x

theorem actualRepairModelPairedFamily_smooth_metric
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b) :
    ContMDiffOn ((𝓘(ℝ,ProbeParameters r)).prod IT) 𝓘(ℝ,Ey) ∞
      (Function.uncurry (run.actualRepairModelPairedFamily packet b p₀))
      (Metric.ball 0 (actualRepairParameterRadius packet.parameterFamily) ×ˢ univ) ∧
    (∀ u, inducedMetric (I := IT) (run.actualRepairModelPairedFamily packet b p₀ u) =
      packet.metric (actualRepairParameterMap packet.parameterFamily b p₀
        (round4PairedParameterReindex r u))) := by
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hSmooth := actualRepairCenteredFamily_smooth packet.parameterFamily hB b p₀ hp₀ _ hFull.2.1
  exact ⟨actualRepairModel_paired_joint_smooth _ _ hSmooth,fun u => hFull.2.2.1 _⟩

/-- Original C3/C2/C1 tails of the paired actual final map minus its actual
first state, on the complete fixed parameter ball and sampling atlas. -/
theorem actualRepairModelPairedFamily_spatial_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hCap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (u : ProbeParameters r) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let tail := run.actualRepairModelPairedFamily packet b p₀ u -
      actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map (round4PairedParameterReindex r u)
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 3 tail ≤ ENNReal.ofReal (2*C*s^(228/25 : ℝ)) ∧
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (2*C*s^(264/25 : ℝ)) ∧
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (2*C*s^(12 : ℝ)) := by
  exact run.actualRepairModelCentered_spatial_tails packet hK heps hSmall hDisp hTheta hCap
    s hs hstart b p₀ hp₀ (round4PairedParameterReindex r u)
    (by simpa only [LinearIsometryEquiv.norm_map] using hu)

/-- The exact original paired columns have the actual Hessian/value tail
moduli, with no paired-coordinate norm loss or replacement final map. -/
theorem actualRepairModelPairedFamily_response_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hCap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (u : ProbeParameters r) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily)
    (l : Fin r) (phase : Bool) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let tail := fun x => fderiv ℝ (fun v => run.actualRepairModelPairedFamily packet b p₀ v x -
      actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map (round4PairedParameterReindex r v) x)
      u (Pi.single (l,phase) 1)
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (s^(44/5 : ℝ)*actualRepairModelHessianModulus C s) ∧
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (s^(10 : ℝ)*actualRepairModelCOneModulus C s) ∧
    probeAtlasCj A 0 tail ≤ ENNReal.ofReal (s^(56/5 : ℝ)*actualRepairModelValueModulus C s) := by
  intro A tail C
  let actualTail := fun z => (initial.map z+∑' j, run.increment packet j z)-initial.map z
  let F := actualRepairCenteredFamily packet.parameterFamily b p₀ actualTail
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ actualTail := hFull.2.1.sub initial.smooth
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hF := actualRepairCenteredFamily_smooth packet.parameterFamily hB b p₀ hp₀ actualTail hSmooth
  have heq : tail = fun x => fderiv ℝ (fun v => F v x) (round4PairedParameterReindex r u)
      (Pi.single (round4PairedParameterIndex r (l,phase)) 1) :=
    actualRepairModel_paired_column_field A
      (actualRepairSamplingAtlas_smooth Data.atlas packet.domain.atlas_smooth packet.Omega packet.source_target)
      (actualRepairSamplingAtlas_support_cover Data.atlas packet.Omega packet.source_sampling)
      (actualRepairParameterRadius packet.parameterFamily) F hF u hu l phase
  rw [heq]
  exact run.actualRepairModelCentered_response_tails packet hK heps hSmall hDisp hTheta hCap
    s hs hstart b p₀ hp₀ (round4PairedParameterReindex r u)
    (by simpa only [LinearIsometryEquiv.norm_map] using hu) (round4PairedParameterIndex r (l,phase))

/-- Every original paired parameter direction satisfies the actual C1/C2
tail budgets. The only finite factor is the number of parameter coordinates. -/
theorem actualRepairModelPairedFamily_direction_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hCap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (u : ProbeParameters r) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily)
    (direction : ProbeParameters r) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let tail := fun x => fderiv ℝ (fun v => run.actualRepairModelPairedFamily packet b p₀ v x -
      actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map (round4PairedParameterReindex r v) x) u direction
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (((Fintype.card (Fin r × Bool)) : ℝ)*(s^(10 : ℝ)*actualRepairModelCOneModulus C s)*‖direction‖) ∧
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (((Fintype.card (Fin r × Bool)) : ℝ)*(s^(44/5 : ℝ)*actualRepairModelHessianModulus C s)*‖direction‖) := by
  intro A tail C
  let actualTail := fun z => (initial.map z+∑' j, run.increment packet j z)-initial.map z
  let F := actualRepairCenteredFamily packet.parameterFamily b p₀ actualTail
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ actualTail := hFull.2.1.sub initial.smooth
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hF := actualRepairCenteredFamily_smooth packet.parameterFamily hB b p₀ hp₀ actualTail hSmooth
  have heq : tail = fun x => fderiv ℝ (fun v => F v x) (round4PairedParameterReindex r u)
      (round4PairedParameterReindex r direction) :=
    actualRepairModel_paired_parameter_field A
      (actualRepairSamplingAtlas_smooth Data.atlas packet.domain.atlas_smooth packet.Omega packet.source_target)
      (actualRepairSamplingAtlas_support_cover Data.atlas packet.Omega packet.source_sampling)
      (actualRepairParameterRadius packet.parameterFamily) F hF u hu direction
  rw [heq]
  simpa only [A,C,F,actualTail,actualRepairCenteredFamily,LinearIsometryEquiv.norm_map] using
    run.actualRepairModelCentered_direction_tails packet hK heps hSmall hDisp hTheta hCap
      s hs hstart b p₀ hp₀ (round4PairedParameterReindex r u)
      (by simpa only [LinearIsometryEquiv.norm_map] using hu) (round4PairedParameterReindex r direction)

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelPairedFamily_smooth_metric
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelPairedFamily_spatial_tails
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelPairedFamily_response_tails
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelPairedFamily_direction_tails

