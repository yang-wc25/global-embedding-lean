import Repair.EntranceCanonicalNamedCosts
import Repair.ReferenceCanonicalReservedCosts
import Repair.EntranceReferenceEnvelopeCosts
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
private local instance entranceCanonicalEnvelopeReservedChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
private local instance entranceCanonicalEnvelopeReservedIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




theorem repairEntranceCanonical_reserved_envelope_costs_before_metric [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ)
    (q : ℕ) (hq : 1 ≤ q) (budget : ℝ) (hbudget : 0 < budget)
    (envelope : ℕ → ℝ) (hEnvelope : ∀ j, packet.closedReferenceProfile j ≤ envelope j) :
    let baseTarget := fun j => round4SpatialPairConstant (m+1) d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j q
    let Ctarget := repairEntranceCompensatedTargetCost baseTarget packet.closedReferenceProfile envelope budget
    (∀ j, 0 ≤ Ctarget j) ∧
    ∀ profile : Round3RepairPrimitiveProfiles,
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius
      BS0 TS0 BP0 TP0 Ds Dp q envelope budget
    ∃ cost : Round3RepairPrimitiveCosts,
    RepairEntranceCanonicalCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr) B0 q hq profile cost ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    let changed := packet.withMetric metric hSym hSmooth
    ∃ reserved : ReferenceCanonicalRepairReservedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      changed profile q hq budget,
      reserved.generated.targetCost=Ctarget ∧ reserved.generated.cost=cost := by
  intro baseTarget Ctarget
  obtain ⟨hBaseTarget,hTarget⟩ := packet.round4_closed_actual_target_data_before_metric hBS0 hTS0 hBP0 hTP0 hK q
  have hCtarget : ∀ j, 0 ≤ Ctarget j := fun j =>
    repairEntranceCompensatedTargetCost_nonneg baseTarget packet.closedReferenceProfile envelope budget
      (hBaseTarget j) (hEnvelope j) hbudget
  have hEnvelopeIdentity (j : ℕ) : Ctarget j*budget+(j+1)*packet.closedReferenceProfile j =
      baseTarget j*budget+(j+1)*envelope j :=
    repairEntranceCompensatedTargetCost_identity baseTarget packet.closedReferenceProfile envelope budget hbudget.ne' j
  refine ⟨hCtarget,?_⟩
  intro profile B0
  let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (Tr := Tr)
    q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  let Theta := parameterRound2_uniformMeanThreshold B0 Csize profile.rho q (q+4)
  let Cmean := incrementCanonical_round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (Tr := Tr)
    B0 q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Dinput profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  let Cmap := repairEntranceCanonicalStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg
  let Cmetric := repairEntranceCanonicalStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg Cmean
  obtain ⟨hTheta,hTheta1,hCmap,hCmetric,hGlobal⟩ :=
    repairEntranceCanonical_uniform_actual_global_increment_named_costs.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
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
    have hUniformBound : ∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas
        changed.parameterFamily.chart changed.closedSamples univ changed.closedSamples_compact
        (fun _ _ hy => hy.1) state.ell j H ≤ B0 j := by
      intro j
      apply (hHbound j).trans
      change baseTarget j*budget+(j+1)*packet.closedReferenceProfile j ≤
        baseTarget j*budget+(j+1)*envelope j
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hEnvelope j) (show (0 : ℝ) ≤ j+1 by positivity))
    refine ⟨{ slice_smooth := hF
              H := H
              target_eq := hH
              input := ?_ },hUniformBound⟩
    exact hGlobal P Λ Β SubSecondary Data.parameterCount Data.atlas changed.parameterFamily.chart
      changed.domain.atlas_smooth hB changed.closedSamples univ isOpen_univ hCover
      changed.closedSamples_compact (fun _ _ hy => hy.1) state.ell state.ell_pos
      (state.ell_le_t.trans state.t_le_one) H hUniformBound
      (fun p x => state.smoothedMap changed (p,x)) hF
  let generated : ReferenceCanonicalRepairGeneratedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      changed profile q hq budget :=
    { targetCost := Ctarget
      target_nonneg := hCtarget
      cost := cost
      profiles := by simp [cost,Round3RepairPrimitiveCosts.UsesProfiles,Round3RepairPrimitiveProfiles.withUniform]
      named_threshold := by
        change parameterRound2_uniformMeanThreshold B0 Csize profile.rho q (q+4) = _
        congr 1
        funext j
        exact (hEnvelopeIdentity j).symm
      data := fun state => Classical.choose (hBundle state) }
  exact ⟨{ generated := generated
           target_budget := by
             intro state j
             change parameterRound2_originalTensorGermSeminorm Data.atlas changed.parameterFamily.chart
               changed.closedSamples univ changed.closedSamples_compact (fun _ _ hy => hy.1)
               state.ell j (Classical.choose (hBundle state)).H ≤
               Ctarget j*budget+(j+1)*packet.closedReferenceProfile j
             rw [hEnvelopeIdentity]
             exact Classical.choose_spec (hBundle state) j },rfl,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceCompensatedTargetCost_identity
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_reserved_envelope_costs_before_metric
