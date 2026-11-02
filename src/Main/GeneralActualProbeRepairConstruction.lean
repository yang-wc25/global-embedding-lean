import NormalPolar.ActualProbeRepairRealization
import Main.GeneralActualProbeFirstModelBounds
import NormalPolar.ActualProbeReserveSelection

/-! Full original domain input from the actual first state and actual repair trajectories. -/

noncomputable section
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
private local instance generalActualProbeRepairConstructionChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance generalActualProbeRepairConstructionIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) (Fintype.card (Fin r × Bool)) N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

variable [CompactSpace M]
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

namespace ActualProbeRepairRealization
variable {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta threshold : ℝ} {b : Fin Data.parameterCount} {p₀ : P}
  {F G : ℝ → ProbeParameters r → M → EuclideanSpace ℝ (Fin N)}
  (realization : ActualProbeRepairRealization (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta threshold b p₀ F G)

/-- Assemble a complete domain input from actual first-state bounds and
actual fixed-cost repair trajectories. Joint smoothness, exact metric,
all four final norms, both native correction tails and the polar reserve
are conclusions. The threshold is selected here, before an original probe
is constructed; the parameter ball and actual admitted slices are retained. -/
def toGeneralDomainModelData
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ k, sigma k ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ k, sigma k ≤ epsilon/(8*((cost k).Cmap ((10+k)/2)+1)))
    (hTheta : ∀ k, sigma k < (cost k).Theta^10)
    (hCap : ∀ k, sigma k ≤ round4ParameterProbeTailCap cost k)
    (hp₀ : p₀ ∈ packet.parameterFamily.inner b) (hT : 0 < threshold)
    (F₀ : M → Ey) (hF₀ : ContMDiff IT 𝓘(ℝ,Ey) ∞ F₀)
    (hi₀ : ∀ x, Function.Injective (mfderiv IT 𝓘(ℝ,Ey) F₀ x))
    (hmetric : ∀ p, packet.metric p = inducedMetric (I := IT) F₀)
    (waves : Fin r → OpenSupportedLegalWave F₀ hF₀)
    (first : GeneralActualProbeFirstModelBounds F₀ hF₀
      (actualRepairSamplingAtlas Data.atlas packet.Omega) waves G
      (actualRepairParameterRadius packet.parameterFamily) threshold) :
    GeneralNativeProbeDomainModelData F₀ hF₀
      (actualRepairSamplingAtlas Data.atlas packet.Omega)
      (actualRepairSamplingAtlas_smooth Data.atlas packet.domain.atlas_smooth packet.Omega packet.source_target)
      (actualRepairSamplingAtlas_support_compact Data.atlas packet.Omega packet.source_compact packet.source_target)
      (actualRepairSamplingAtlas_support_cover Data.atlas packet.Omega packet.source_sampling) hi₀ waves := by
  let A := actualRepairSamplingAtlas Data.atlas packet.Omega
  let hA := actualRepairSamplingAtlas_smooth Data.atlas packet.domain.atlas_smooth packet.Omega packet.source_target
  let hc := actualRepairSamplingAtlas_support_compact Data.atlas packet.Omega packet.source_compact packet.source_target
  let hcov := actualRepairSamplingAtlas_support_cover Data.atlas packet.Omega packet.source_sampling
  let Ct := round4ParameterProbeTailConstant cost
  let C := actualRepairUniformBudget first.constant Ct threshold (Fintype.card (Fin r × Bool))
  let K := originalC2PolarConstant A hA hc hcov F₀ hF₀ hi₀
  let T := actualProbeReserveThreshold threshold K C
  have hCt : 0 ≤ Ct := (round4ParameterProbeTailConstant_pos cost).le
  have hC : 0 ≤ C := actualRepairUniformBudget_nonneg first.constant_nonneg hCt _
  have hKpos : 0 ≤ K := (originalC2PolarConstant_pos A hA hc hcov F₀ hF₀ hi₀).le
  have hmodelC : first.constant ≤ C := by
    unfold C actualRepairUniformBudget
    exact le_add_of_nonneg_right (by positivity)
  have hOld {s : ℝ} (hsT : s < T) : s < threshold :=
    hsT.trans_le (actualProbeReserveThreshold_le threshold K C)
  have hfinal (s : ℝ) (hs : 0 < s) (hsT : s < threshold)
      (u : ProbeParameters r) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily) :=
    realization.final_budgets packet hK heps hSmall hDisp hTheta hCap hp₀
      F₀ hF₀ first.constant first.constant_nonneg s hs hsT u hu
      (first.closeness s hs hsT u hu) (first.spatial_C3 s hs hsT u hu)
      (first.parameter_C1 s hs hsT u hu) (first.parameter_C2 s hs hsT u hu)
  have hsmooth (s : ℝ) (hs : 0 < s) (hsT : s < T) :=
    realization.smooth_metric packet hK heps hSmall hDisp hTheta hp₀ s hs (hOld hsT)
  refine {
    radius := actualRepairParameterRadius packet.parameterFamily
    radius_pos := actualRepairParameterRadius_pos packet.parameterFamily
    threshold := T
    threshold_pos := actualProbeReserveThreshold_pos hT hKpos hC
    map := F
    model := G
    joint_smooth := fun s hs hsT => (hsmooth s hs hsT).1
    model_joint_smooth := fun s hs hsT => (hsmooth s hs hsT).2.1
    metric := ?_
    weight := first.weight
    weight_pos := first.weight_pos
    distinct_on_overlap := first.distinct_on_overlap
    constant := C
    constant_nonneg := hC
    modelHConstant := first.constant
    tailHConstant := 0
    modelVConstant := first.constant
    tailVConstant := 0
    modelHConstant_nonneg := first.constant_nonneg
    tailHConstant_nonneg := le_rfl
    modelVConstant_nonneg := first.constant_nonneg
    tailVConstant_nonneg := le_rfl
    hessian_coefficient_le := by simpa only [mul_zero,add_zero] using hmodelC
    value_coefficient_le := by simpa only [mul_zero,add_zero] using hmodelC
    etaModelH := first.etaH
    etaTailH := actualRepairModelHessianModulus Ct
    etaModelV := first.etaV
    etaTailV := actualRepairModelValueModulus Ct
    etaModelH_nonneg := first.etaH_nonneg
    etaTailH_nonneg := fun s => (actualRepairModel_moduli_nonneg hCt s).1
    etaModelV_nonneg := first.etaV_nonneg
    etaTailV_nonneg := fun s => (actualRepairModel_moduli_nonneg hCt s).2.2
    etaModelH_tendsto := first.etaH_tendsto
    etaTailH_tendsto := (actualRepairModel_moduli_tendsto Ct).1
    etaModelV_tendsto := first.etaV_tendsto
    etaTailV_tendsto := (actualRepairModel_moduli_tendsto Ct).2.2
    closeness := fun s hs hsT u hu => (hfinal s hs (hOld hsT) u hu).1
    spatial_C3 := fun s hs hsT u hu => (hfinal s hs (hOld hsT) u hu).2.1
    parameter_C1 := fun s hs hsT u hu => (hfinal s hs (hOld hsT) u hu).2.2.1
    parameter_C2 := fun s hs hsT u hu => (hfinal s hs (hOld hsT) u hu).2.2.2
    model_hessian_response := fun s hs hsT => first.hessian_response s hs (hOld hsT)
    model_value_response := fun s hs hsT => first.value_response s hs (hOld hsT)
    hessian_tail := ?_
    value_tail := ?_
    reserve := (1 : ℝ)/2
    reserve_lt_one := by norm_num
    closeness_reserve := ?_ }
  · intro s hs hsT u _hu x
    have h := (hsmooth s hs hsT).2.2 u
    rw [hmetric] at h
    exact congrFun h x
  · intro s hs hsT u hu l phase
    simpa only [zero_mul, add_zero] using
      (realization.response_tails packet hK heps hSmall hDisp hTheta hCap hp₀
        s hs (hOld hsT) u hu l phase).1
  · intro s hs hsT u hu l phase
    simpa only [zero_mul, add_zero] using
      (realization.response_tails packet hK heps hSmall hDisp hTheta hCap hp₀
        s hs (hOld hsT) u hu l phase).2.2
  · intro s hs hsT
    refine ⟨C*s^(44/5 : ℝ), by positivity, ?_, ?_⟩
    · intro u hu
      exact (hfinal s hs (hOld hsT) u hu).1
    · exact actualProbeReserveThreshold_budget hKpos hC s hs hsT

end ActualProbeRepairRealization
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ActualProbeRepairRealization.toGeneralDomainModelData
