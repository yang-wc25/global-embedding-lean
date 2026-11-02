import Repair.EntranceCanonicalGlobalCosts
import Probes.Round3RepairGeneratedCosts

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

def RepairEntranceCanonicalCostIdentity (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (profile : Round3RepairPrimitiveProfiles) (cost : Round3RepairPrimitiveCosts) : Prop :=
  let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (Tr := Tr)
    q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  let Cmean := incrementCanonical_round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (Tr := Tr)
    B0 q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
    profile.Dinput profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg
  cost.Theta = parameterRound2_uniformMeanThreshold B0 Csize profile.rho q (q+4) ∧
  cost.Cmap = repairEntranceCanonicalStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg ∧
  cost.Cmetric = repairEntranceCanonicalStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr)
    q profile.Rsub profile.Lprimary profile.Rsecondary hq profile.reserve profile.reserve_pos
    profile.Bsec profile.Msec profile.Ccut profile.Tsec profile.Tinv profile.Tobs
    profile.Bsec_nonneg profile.Msec_nonneg profile.Ccut_nonneg
    profile.Tsec_nonneg profile.Tinv_nonneg profile.Tobs_nonneg Cmean

theorem repairEntranceCanonical_numeric_costs_exists
    (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (profile : Round3RepairPrimitiveProfiles) :
    ∃ cost : Round3RepairPrimitiveCosts,
      RepairEntranceCanonicalCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
        (m := m) (d := d) (N := N) (Tr := Tr) B0 q hq profile cost := by
  let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (Tr := Tr)
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
  obtain ⟨hTheta,hTheta1⟩ := parameterRound2_uniformMeanThreshold_pos
    B0 Csize profile.rho profile.rho_pos q (q+4)
  have hCmap (j : ℕ) : 0 ≤ Cmap j := repairEntranceCanonicalRawMapCost_nonneg
    (m := m) (d := d) (N := N) (Tr := Tr)
    (j+2*q+8) (j+q+4) j q profile.Rsub profile.Lprimary profile.Rsecondary hq (by omega) (by omega)
    profile.reserve (profile.Bsec j) (profile.Msec j) (profile.Ccut j) profile.reserve_pos
    (profile.Bsec_nonneg j) (profile.Msec_nonneg j) (profile.Ccut_nonneg j)
    (profile.Tsec j) (profile.Tinv j) (profile.Tobs j)
    (profile.Tsec_nonneg j) (profile.Tinv_nonneg j) (profile.Tobs_nonneg j)
  have hCmean (j : ℕ) : 0 ≤ Cmean j := by
    apply parameterRound2_finiteMeanErrorCost_nonneg
    · exact fun _ => le_max_left _ _
    · exact fun _ _ => le_max_left _ _
  have hCmetric (j : ℕ) : 0 ≤ Cmetric j := add_nonneg
    (repairEntranceCanonicalRawMetricCost_nonneg
      (m := m) (d := d) (N := N) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q profile.Rsub profile.Lprimary profile.Rsecondary hq (by omega) (by omega)
      profile.reserve (profile.Bsec j) (profile.Msec j) (profile.Ccut j) profile.reserve_pos
      (profile.Bsec_nonneg j) (profile.Msec_nonneg j) (profile.Ccut_nonneg j)
      (profile.Tsec j) (profile.Tinv j) (profile.Tobs j)
      (profile.Tsec_nonneg j) (profile.Tinv_nonneg j) (profile.Tobs_nonneg j)) (hCmean j)
  exact ⟨profile.withUniform Theta hTheta hTheta1 Cmap Cmetric hCmap hCmetric,rfl,rfl,rfl⟩

def repairEntranceCanonicalNumericCosts
    (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (profile : Round3RepairPrimitiveProfiles) :
    Round3RepairPrimitiveCosts :=
  Classical.choose (repairEntranceCanonical_numeric_costs_exists.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr) B0 q hq profile)

theorem repairEntranceCanonicalNumericCosts_identity
    (B0 : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) (profile : Round3RepairPrimitiveProfiles) :
    RepairEntranceCanonicalCostIdentity.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr) B0 q hq profile
      (repairEntranceCanonicalNumericCosts.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
        (m := m) (d := d) (N := N) (Tr := Tr) B0 q hq profile) :=
  Classical.choose_spec (repairEntranceCanonical_numeric_costs_exists.{uM,uP,uTr,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := Tr) B0 q hq profile)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_numeric_costs_exists
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonicalNumericCosts_identity
