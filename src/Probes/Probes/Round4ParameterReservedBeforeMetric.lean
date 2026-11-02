import Probes.Round4ParameterFiniteRepairFactory
import Probes.Round3RepairReservedBeforeMetric

/-!
# Named finite repair costs before the prescribed metric

The same actual target coefficient, global mean iteration and single U
are chosen before any target metric. The original reserved-data structure
is populated with the named finite map and metric costs, retaining its
actual target budget on every future closed-domain repair state.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round4ParameterReservedBeforeMetricChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterReservedBeforeMetricIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- The actual threshold and all-order output coefficients used by a repair
cost record, with no arbitrary numerical witness left in these fields. -/
def Round4ParameterRepairCostIdentity (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (profile : Round3RepairPrimitiveProfiles) (cost : Round3RepairPrimitiveCosts) : Prop :=
  let Csize := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  let Cmean := round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    B0 q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Dinput profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  cost.Theta = parameterRound2_uniformMeanThreshold B0 Csize profile.rho q (q+4) ∧
  cost.Cmap = round4ParameterStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg ∧
  cost.Cmetric = round4ParameterStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg Cmean

theorem Round3RepairFixedSmoothingPacket.round4_closed_actual_target_data_before_metric [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (r : ℕ) :
    let Ctarget := fun j => round4SpatialPairConstant (m+1) d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
    (∀ j, 0 ≤ Ctarget j) ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    let changed := packet.withMetric metric hSym hSmooth
    ∀ (budget : ℝ) (state : Round3RepairCurrentSmoothingState changed r budget),
      ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (state.smoothedMap changed) ∧
      (∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => state.smoothedMap changed (p,x))) ∧
      ∃ H : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ,
        H.val=state.computedTarget changed ∧
        ∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
          packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell j H ≤
          Ctarget j*budget+(j+1)*packet.closedReferenceProfile j := by
  intro Ctarget
  refine ⟨(packet.round4_closed_actual_target_data hBS0 hTS0 hBP0 hTP0 hK r).1,?_⟩
  intro metric hSym hSmooth changed
  exact (changed.round4_closed_actual_target_data hBS0 hTS0 hBP0 hTP0 hK r).2

theorem round4Parameter_reserved_named_costs_before_metric [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ)
    (q : ℕ) (hq : 1 ≤ q) (budget : ℝ) :
    let Ctarget := fun j => round4SpatialPairConstant (m+1) d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
    (∀ j, 0 ≤ Ctarget j) ∧
    ∀ profile : Round3RepairPrimitiveProfiles,
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS0 TS0 BP0 TP0 Ds Dp q packet.closedReferenceProfile budget
    ∃ cost : Round3RepairPrimitiveCosts,
    Round4ParameterRepairCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr) B0 q hq profile cost ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    let changed := packet.withMetric metric hSym hSmooth
    ∃ reserved : Round3RepairReservedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      changed profile q hq budget,
      reserved.generated.targetCost=Ctarget ∧ reserved.generated.cost=cost := by
  intro Ctarget
  obtain ⟨hCtarget,hTarget⟩ := packet.round4_closed_actual_target_data_before_metric hBS0 hTS0 hBP0 hTP0 hK q
  refine ⟨hCtarget,?_⟩
  intro profile B0
  let Csize := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  let Theta := parameterRound2_uniformMeanThreshold B0 Csize profile.rho q (q+4)
  let Cmean := round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    B0 q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Dinput profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  let Cmap := round4ParameterStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg
  let Cmetric := round4ParameterStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg Cmean
  obtain ⟨hTheta,hTheta1,hCmap,hCmetric,hGlobal⟩ :=
    round4Parameter_uniform_actual_global_increment_named_costs.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 profile.rho profile.rho_pos q profile.Rsub profile.Lprimary profile.Rsecondary hq
      profile.reserve profile.reserve_pos profile.Bnd profile.Mg profile.Dinput
      profile.Bnd_nonneg profile.Mg_nonneg profile.Dinput_nonneg profile.T profile.T_nonneg
      profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
      profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
      profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg
  let cost := profile.withUniform Theta hTheta hTheta1 Cmap Cmetric hCmap hCmetric
  refine ⟨cost,⟨rfl,rfl,rfl⟩,?_⟩
  intro metric hSym hSmooth changed
  have hB : ∀ i, changed.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [changed.chart_eq]
    exact changed.domain.parameter_charts_smooth
  have hCover : ∀ z ∈ (univ : Set (P × M)), ∃ b, z.1 ∈ (changed.parameterFamily.chart b).source := by
    intro z _
    obtain ⟨b,hb,_⟩ := changed.domain.parameter_cover z.1 (by rw [hK]; exact mem_univ _)
    exact ⟨b,by simpa only [changed.chart_eq] using hb⟩
  have hBundle : ∀ state : Round3RepairCurrentSmoothingState changed q budget,
      ∃ data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        changed cost state,
      ∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas changed.parameterFamily.chart changed.closedSamples univ
        changed.closedSamples_compact (fun _ _ hy => hy.1) state.ell j data.H ≤ B0 j := by
    intro state
    obtain ⟨hSF,hF,H,hH,hHbound⟩ := hTarget metric hSym hSmooth budget state
    refine ⟨{ slice_smooth := hF
              H := H
              target_eq := hH
              input := ?_ },hHbound⟩
    exact hGlobal P Λ Β SubSecondary Data.parameterCount Data.atlas changed.parameterFamily.chart
      changed.domain.atlas_smooth hB changed.closedSamples univ isOpen_univ hCover
      changed.closedSamples_compact (fun _ _ hy => hy.1) state.ell state.ell_pos
      (state.ell_le_t.trans state.t_le_one) H hHbound
      (fun p x => state.smoothedMap changed (p,x)) hF
  let generated : Round3RepairGeneratedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      changed profile q hq budget :=
    { targetCost := Ctarget
      target_nonneg := hCtarget
      cost := cost
      profiles := by simp [cost,Round3RepairPrimitiveCosts.UsesProfiles,Round3RepairPrimitiveProfiles.withUniform]
      named_threshold := rfl
      data := fun state => Classical.choose (hBundle state) }
  exact ⟨{ generated := generated
           target_budget := fun state => Classical.choose_spec (hBundle state) },rfl,rfl⟩


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairFixedSmoothingPacket.round4_closed_actual_target_data_before_metric
#print axioms GlobalEmbedding.Continuation.round4Parameter_reserved_named_costs_before_metric
