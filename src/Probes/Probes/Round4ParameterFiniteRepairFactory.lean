import Smoothing.Round3RepairUniformMeanData
import Probes.Round3RepairGeneratedCosts
import Probes.Round4ParameterClosedTargetData
import Probes.Round4ParameterFiniteGlobalConsumer
import Probes.Round4ParameterRepairFinitePrefix

/-!
# Named finite costs consumed by the actual closed-domain repair factory

The target, reserve threshold, mean residual and oscillatory map/metric
profiles are all the named finite-dependence values. The literal same
SF/SH and fixed closed samples supply every non-raw field of the existing
repair mean-data structure. Numerical witnesses are not chosen after the
current state or scale.
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
local instance round4ParameterFiniteRepairChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterFiniteRepairIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- The numerical threshold and all displacement/metric constants are
selected internally, before the current map and scale, from fixed primitive
profiles and the actual closed-domain target gain.  The current SF/SH then
supplies every non-raw entrance field of the mean/oscillatory constructor. -/
theorem round4_repair_uniform_named_costs_from_actual_closed_target [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (q : ℕ) (hq : 1 ≤ q)
    (budget : ℝ) (profile : Round3RepairPrimitiveProfiles) :
    let Ctarget := fun j => round4SpatialPairConstant (m+1) d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
    (∀ j, 0 ≤ Ctarget j) ∧
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS0 TS0 BP0 TP0 Ds Dp q packet.closedReferenceProfile budget
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
    ∃ (hTheta : 0 < Theta) (hTheta1 : Theta ≤ 1),
    ∃ (hCmap : ∀ j, 0 ≤ Cmap j) (hCmetric : ∀ j, 0 ≤ Cmetric j),
    let cost := profile.withUniform Theta hTheta hTheta1 Cmap Cmetric hCmap hCmetric
    ∀ state : Round3RepairCurrentSmoothingState packet q budget,
      Nonempty (Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
        packet cost state) := by
  intro Ctarget
  obtain ⟨hCtarget,hTarget⟩ := packet.round4_closed_actual_target_data hBS0 hTS0 hBP0 hTP0 hK q
  refine ⟨hCtarget,?_⟩
  intro B0 Csize Theta Cmean Cmap Cmetric
  obtain ⟨hTheta,hTheta1,hCmap,hCmetric,hGlobal⟩ :=
    round4Parameter_uniform_actual_global_increment_named_costs.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 profile.rho profile.rho_pos q profile.Rsub profile.Lprimary profile.Rsecondary hq
      profile.reserve profile.reserve_pos profile.Bnd profile.Mg profile.Dinput
      profile.Bnd_nonneg profile.Mg_nonneg profile.Dinput_nonneg profile.T profile.T_nonneg
      profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
      profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
      profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg
  refine ⟨hTheta,hTheta1,hCmap,hCmetric,?_⟩
  intro cost state
  obtain ⟨hSF,hF,H,hH,hHbound⟩ := hTarget budget state
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hCover : ∀ z ∈ (univ : Set (P × M)), ∃ b, z.1 ∈ (packet.parameterFamily.chart b).source := by
    intro z _
    obtain ⟨b,hb,_⟩ := packet.domain.parameter_cover z.1 (by rw [hK]; exact mem_univ _)
    exact ⟨b,by simpa only [packet.chart_eq] using hb⟩
  refine ⟨{ slice_smooth := hF
            H := H
            target_eq := hH
            input := ?_ }⟩
  exact hGlobal P Λ Β SubSecondary Data.parameterCount Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.closedSamples univ isOpen_univ hCover
    packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell state.ell_pos
    (state.ell_le_t.trans state.t_le_one) H hHbound
    (fun p x => state.smoothedMap packet (p,x)) hF

/-- The existing repair generated-data type is inhabited with precisely
these named finite-dependence target, map and metric profiles. -/
theorem round4_repair_generate_named_costs [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (q : ℕ) (hq : 1 ≤ q)
    (budget : ℝ) (profile : Round3RepairPrimitiveProfiles) :
    let Ctarget := fun j => round4SpatialPairConstant (m+1) d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS0 TS0 BP0 TP0 Ds Dp q packet.closedReferenceProfile budget
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
    ∃ generated : Round3RepairGeneratedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget,
      generated.targetCost = Ctarget ∧ generated.cost.Cmap = Cmap ∧ generated.cost.Cmetric = Cmetric := by
  intro Ctarget B0 Csize Theta Cmean Cmap Cmetric
  obtain ⟨hCtarget,hTheta,hTheta1,hCmap,hCmetric,hData⟩ :=
    round4_repair_uniform_named_costs_from_actual_closed_target
      (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet hBS0 hTS0 hBP0 hTP0 hK q hq budget profile
  refine ⟨{ targetCost := Ctarget
            target_nonneg := hCtarget
            cost := profile.withUniform Theta hTheta hTheta1 Cmap Cmetric hCmap hCmetric
            profiles := ?_
            named_threshold := rfl
            data := fun state => Classical.choice (hData state) },rfl,rfl,rfl⟩
  simp [Round3RepairPrimitiveCosts.UsesProfiles,Round3RepairPrimitiveProfiles.withUniform]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_repair_uniform_named_costs_from_actual_closed_target

#print axioms GlobalEmbedding.Continuation.round4_repair_generate_named_costs
