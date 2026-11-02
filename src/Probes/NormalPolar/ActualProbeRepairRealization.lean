import NormalPolar.ActualRepairSameRunBudgets

/-! Actual whole-scale realization by the same fixed-cost repair trajectories. -/

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
local instance actualProbeRepairRealizationChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualProbeRepairRealizationIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) (Fintype.card (Fin r × Bool)) N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

variable [CompactSpace M]
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

/-- Realization by one genuine initial state and one genuine run at each
admitted scale. The numerical costs and source/parameter packet are fixed
before the scale. Map identities are identities of entire source families;
no final estimate or normal identification is included in this predicate. -/
structure ActualProbeRepairRealization
    (cost : ℕ → Round3RepairPrimitiveCosts) (Cs : ℕ → ℕ → ℝ) (sigma : ℕ → ℝ)
    (budget epsilon eta threshold : ℝ)
    (b : Fin Data.parameterCount) (p₀ : P)
    (F G : ℝ → ProbeParameters r → M → Ey) : Prop where
  atScale : ∀ (s : ℝ) (hs : 0 < s), s < threshold →
    ∃ (hs1 : s^(6/5 : ℝ) < 1)
      (initial : Round3RepairClosedState packet budget epsilon eta 10 (s^(6/5 : ℝ)))
      (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        packet cost Cs sigma budget epsilon eta (s^(6/5 : ℝ))
        (Real.rpow_pos_of_pos hs _) hs1 initial),
      F s = run.actualRepairModelPairedFamily packet b p₀ ∧
      G s = fun u => actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map
        (round4PairedParameterReindex r u)


namespace ActualProbeRepairRealization
variable {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta threshold : ℝ} {b : Fin Data.parameterCount} {p₀ : P}
  {F G : ℝ → ProbeParameters r → M → EuclideanSpace ℝ (Fin N)}
  (realization : ActualProbeRepairRealization (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta threshold b p₀ F G)

include realization

/-- Both actual maps inherit their joint smoothness, and the final map has
exactly the prescribed metric of that same trajectory. -/
theorem smooth_metric
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (s : ℝ) (hs : 0 < s) (hsT : s < threshold) :
    ContMDiffOn ((𝓘(ℝ,ProbeParameters r)).prod IT) 𝓘(ℝ,Ey) ∞
      (Function.uncurry (F s))
      (Metric.ball 0 (actualRepairParameterRadius packet.parameterFamily) ×ˢ univ) ∧
    ContMDiffOn ((𝓘(ℝ,ProbeParameters r)).prod IT) 𝓘(ℝ,Ey) ∞
      (Function.uncurry (G s))
      (Metric.ball 0 (actualRepairParameterRadius packet.parameterFamily) ×ˢ univ) ∧
    (∀ u, inducedMetric (I := IT) (F s u) =
      packet.metric (actualRepairParameterMap packet.parameterFamily b p₀
        (round4PairedParameterReindex r u))) := by
  obtain ⟨hs1, initial, run, hF, hG⟩ := realization.atScale s hs hsT
  rw [hF, hG]
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hinit := actualRepairModel_paired_joint_smooth
    (actualRepairParameterRadius packet.parameterFamily)
    (actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map)
    (actualRepairCenteredFamily_smooth packet.parameterFamily hB b p₀ hp₀ initial.map initial.smooth)
  have hfinal := run.actualRepairModelPairedFamily_smooth_metric packet hK heps hSmall hDisp hTheta b p₀ hp₀
  exact ⟨hfinal.1, hinit, hfinal.2⟩

/-- Literal H/C1/value response tails from the same realization, with
constants and moduli independent of the later scale and probe parameters. -/
theorem response_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hCap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k)
    (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (s : ℝ) (hs : 0 < s) (hsT : s < threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily)
    (l : Fin r) (phase : Bool) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let tail := fun x => fderiv ℝ (fun v => F s v x-G s v x) u (Pi.single (l,phase) 1)
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (s^(44/5 : ℝ)*actualRepairModelHessianModulus C s) ∧
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (s^(10 : ℝ)*actualRepairModelCOneModulus C s) ∧
    probeAtlasCj A 0 tail ≤ ENNReal.ofReal (s^(56/5 : ℝ)*actualRepairModelValueModulus C s) := by
  obtain ⟨hs1, initial, run, hF, hG⟩ := realization.atScale s hs hsT
  rw [hF, hG]
  exact run.actualRepairModelPairedFamily_response_tails packet hK heps hSmall hDisp hTheta hCap
    s hs rfl b p₀ hp₀ u hu l phase

/-- Final original budgets are proved from the actual model budgets. This
realization contains no final-budget field and no tail-budget field. -/
theorem final_budgets
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hCap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k)
    (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (F₀ : M → Ey) (hF₀ : ContMDiff IT 𝓘(ℝ,Ey) ∞ F₀)
    (Cmodel : ℝ) (hCmodel : 0 ≤ Cmodel)
    (s : ℝ) (hs : 0 < s) (hsT : s < threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let C := actualRepairUniformBudget Cmodel (round4ParameterProbeTailConstant cost)
      threshold (Fintype.card (Fin r × Bool))
    probeAtlasCj A 2 (G s u-F₀) ≤ ENNReal.ofReal (Cmodel*s^(44/5 : ℝ)) →
    probeAtlasCj A 3 (G s u) ≤ ENNReal.ofReal Cmodel →
    (∀ v, probeAtlasCj A 1 (fun x => fderiv ℝ (fun w => G s w x) u v) ≤
      ENNReal.ofReal (Cmodel*s^(10 : ℕ)*‖v‖)) →
    (∀ v, probeAtlasCj A 2 (fun x => fderiv ℝ (fun w => G s w x) u v) ≤
      ENNReal.ofReal (Cmodel*s^(44/5 : ℝ)*‖v‖)) →
    probeAtlasCj A 2 (F s u-F₀) ≤ ENNReal.ofReal (C*s^(44/5 : ℝ)) ∧
    probeAtlasCj A 3 (F s u) ≤ ENNReal.ofReal C ∧
    (∀ v, probeAtlasCj A 1 (fun x => fderiv ℝ (fun w => F s w x) u v) ≤
      ENNReal.ofReal (C*s^(10 : ℕ)*‖v‖)) ∧
    (∀ v, probeAtlasCj A 2 (fun x => fderiv ℝ (fun w => F s w x) u v) ≤
      ENNReal.ofReal (C*s^(44/5 : ℝ)*‖v‖)) := by
  obtain ⟨hs1, initial, run, hF, hG⟩ := realization.atScale s hs hsT
  rw [hF, hG]
  exact run.actualRepairModelPairedFamily_final_budgets packet hK heps hSmall hDisp hTheta hCap
    F₀ hF₀ Cmodel threshold s hCmodel hs hsT rfl b p₀ hp₀ u hu

end ActualProbeRepairRealization
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ActualProbeRepairRealization.smooth_metric
#print axioms GlobalEmbedding.Continuation.ActualProbeRepairRealization.response_tails
#print axioms GlobalEmbedding.Continuation.ActualProbeRepairRealization.final_budgets
