import Repair.ReferenceCanonicalMeanEntrance

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
local instance referenceCanonicalMeanProfileChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance referenceCanonicalMeanProfileIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




namespace ReferenceCanonicalRepairReservedCosts
/-- The original finite iteration profile, selected numerically before SF,
H, the current state and the oscillatory scale. -/
def iterateProfile (profile : Round3RepairPrimitiveProfiles) {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (reserved : ReferenceCanonicalRepairReservedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget) : ℕ → ℝ :=
  let B0 := fun j => reserved.generated.targetCost j*budget+(j+1)*packet.closedReferenceProfile j
  let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (Tr := Tr)
    q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
      profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  parameterRound2_uniformMeanProfile B0 Csize (q+4) q
end ReferenceCanonicalRepairReservedCosts

/-- Every original seminorm of the same canonical Kq is bounded by a
preselected numerical profile, independently of secondary raw data. -/
theorem referenceCanonical_round3_repair_generated_mean_iterate_profile
    (profile : Round3RepairPrimitiveProfiles) {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (reserved : ReferenceCanonicalRepairReservedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget)
    (state : Round3RepairCurrentSmoothingState packet q budget)
    (witness : Round3RepairRawMeanWitness (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet reserved.generated.cost (reserved.generated.data state))
    (e : ℝ) (he : 0 < e) (heTheta : e < reserved.generated.cost.Theta) :
    let mean := witness.toMean packet
    let p := Round3RepairPrimitiveMeanData.seminorm packet state.ell
    ∀ j, p j (mean.iterate packet e) ≤ reserved.iterateProfile packet profile hq j := by
  intro mean p
  let generated := reserved.generated
  let cost := generated.cost
  let B0 := fun j => generated.targetCost j*budget+(j+1)*packet.closedReferenceProfile j
  rcases generated.profiles with ⟨hRho,hReserve,hRsub,hLprimary,hRsecondary,hBnd,hMg,hDinput,hT,hRest⟩
  have hrho : 0 < cost.rho := by simpa only [cost,hRho] using profile.rho_pos
  have hc : 0 < cost.reserve := by simpa only [cost,hReserve] using profile.reserve_pos
  have hBndNonneg : ∀ j R, 0 ≤ cost.Bnd j R := by simpa only [cost,hBnd] using profile.Bnd_nonneg
  have hMgNonneg : ∀ j, 0 ≤ cost.Mg j := by simpa only [cost,hMg] using profile.Mg_nonneg
  have hDinputNonneg : ∀ j, 0 ≤ cost.Dinput j := by simpa only [cost,hDinput] using profile.Dinput_nonneg
  have hTNonneg : ∀ j, 0 ≤ cost.T j := by simpa only [cost,hT] using profile.T_nonneg
  let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (Tr := Tr)
    q cost.Rsub cost.Lprimary hq cost.reserve hc cost.Bnd cost.Mg hBndNonneg hMgNonneg cost.T hTNonneg
  have hCsize : Csize = incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (Tr := Tr)
      q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
        profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg := by
    dsimp only [Csize]
    congr 1
  have hThreshold : cost.Theta=parameterRound2_uniformMeanThreshold B0 Csize cost.rho q (q+4) := by
    simpa only [cost,B0,hCsize,hRho] using generated.named_threshold
  obtain ⟨hsm,hsize,hdiff⟩ := incrementCanonical_round3Parameter_actual_raw_mean_local_estimates
    Data.atlas packet.parameterFamily.chart packet.domain.atlas_smooth packet.closedSamples univ
    packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell state.ell_pos
    (state.ell_le_t.trans state.t_le_one) mean.H cost.rho q cost.Rsub cost.Lprimary hq cost.reserve hc
    cost.Bnd cost.Mg cost.Dinput hBndNonneg hMgNonneg hDinputNonneg cost.T hTNonneg
    (fun p x => state.smoothedMap packet (p,x)) mean.slice_smooth mean.g mean.chart_preserves mean.primary mean.mean_raw
  have heNamed : e < parameterRound2_uniformMeanThreshold B0 Csize cost.rho q (q+4) := by
    rw [← hThreshold]
    exact heTheta
  have hIter := parameterRound2_uniform_mean_reserve_profile B0 Csize cost.rho hrho q (q+4)
    p mean.H (reserved.target_budget state) (mean.operator packet) hsize e he heNamed
  intro j
  have hBound : p j (mean.iterate packet e) ≤ parameterRound2_uniformMeanProfile B0 Csize (q+4) q j :=
    hIter.2 q (le_refl q) j
  simpa only [ReferenceCanonicalRepairReservedCosts.iterateProfile,B0,generated,hCsize] using hBound

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.referenceCanonical_round3_repair_generated_mean_iterate_profile
