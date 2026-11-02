import Probes.Round4ParameterReservedBeforeMetric

/-!
# A numerical cost prototype selected before any reference map

The prototype is the original finite mean and oscillatory cost formula.
It is chosen without a map, source atlas, parameter manifold, target,
current state, or trajectory, and can therefore fix the entrance first.
The actual reserved factory later identifies its finite cost prefix.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uTr uΛ uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]

theorem repairEntrance_numeric_costs_exists
    (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (profile : Round3RepairPrimitiveProfiles) :
    ∃ cost : Round3RepairPrimitiveCosts,
      Round4ParameterRepairCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
        (m := m) (d := d) (N := N) (M := M) (Tr := Tr) B0 q hq profile cost := by
  let Csize := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
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
  obtain ⟨hTheta,hTheta1,hCmap,hCmetric,_⟩ :=
    round4Parameter_uniform_actual_global_increment_named_costs.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 profile.rho profile.rho_pos q profile.Rsub profile.Lprimary profile.Rsecondary hq
      profile.reserve profile.reserve_pos profile.Bnd profile.Mg profile.Dinput
      profile.Bnd_nonneg profile.Mg_nonneg profile.Dinput_nonneg profile.T profile.T_nonneg
      profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
      profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
      profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg
  exact ⟨profile.withUniform Theta hTheta hTheta1 Cmap Cmetric hCmap hCmetric,rfl,rfl,rfl⟩

def repairEntranceNumericCosts
    (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (profile : Round3RepairPrimitiveProfiles) :
    Round3RepairPrimitiveCosts :=
  Classical.choose (repairEntrance_numeric_costs_exists.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr) B0 q hq profile)

theorem repairEntranceNumericCosts_identity
    (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (profile : Round3RepairPrimitiveProfiles) :
    Round4ParameterRepairCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr) B0 q hq profile
      (repairEntranceNumericCosts.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
        (m := m) (d := d) (N := N) (M := M) (Tr := Tr) B0 q hq profile) :=
  Classical.choose_spec (repairEntrance_numeric_costs_exists.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr) B0 q hq profile)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_numeric_costs_exists
#print axioms GlobalEmbedding.Continuation.repairEntranceNumericCosts_identity
