import Repair.EntranceFiniteNumericalPlan
import Repair.EntranceCanonicalCompletedProfile
import Repair.EntranceCanonicalNamedCosts

/-! Source-independent finite numerical entrance. All values below are fixed
from numerical profiles before any source manifold, atlas, reference map,
metric, current state or orbit is supplied. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
namespace RepairEntranceParameters
universe uM uP uΛ uΒ uSubSecondary
variable {m d N : ℕ} (p : RepairEntranceParameters) (a : RepairEntranceProfiles)

def canonicalCompletedProfile (q : ℕ) (hq : 1 ≤ q) : Round3RepairPrimitiveProfiles :=
  repairEntranceCanonicalCarrierCompletedProfile.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N)
    (p.targetBudget a m d N q) q p.Rsub p.Lprimary p.Rsecondary hq
    p.meanReserve p.meanReserve_pos p.c p.cT
    (p.packet a m d N q) a.Forward a.Inverse a.Meta (p.packet_nonneg a m d N q)
    (p.secondaryGeometry a m d N q) (cutoff a q) a.Tinv a.Tobs

def canonicalCost (q : ℕ) (hq : 1 ≤ q) : Round3RepairPrimitiveCosts :=
  repairEntranceCanonicalNumericCosts.{uM,uP,0,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (Tr := ℝ)
    (p.targetBudget a m d N q) q hq
    (p.canonicalCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) a q hq)

theorem canonicalCost_identity (q : ℕ) (hq : 1 ≤ q) :
    RepairEntranceCanonicalCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := ℝ)
      (p.targetBudget a m d N q) q hq
      (p.canonicalCompletedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) a q hq)
      (p.canonicalCost.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) a q hq) :=
  repairEntranceCanonicalNumericCosts_identity _ _ _ _

def canonicalEntry : ℝ :=
  let c := p.canonicalCost.{uM,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) a 440 (by norm_num)
  min (round4ParameterNumericalBlockScale m d N (p.smoothingCost a m d 440)
    c.Cmap c.Cmetric a.metricReference c.Theta p.budget p.epsilon p.eta 10)
    (p.geometryCap a m d 440/2)

theorem canonicalEntry_pos :
    0 < p.canonicalEntry.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) a := by
  let c := p.canonicalCost.{uM,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) a 440 (by norm_num)
  exact lt_min
    (repairEntrance_numerical_scale_positive m d N 10 (p.smoothingCost a m d 440)
      c.Cmap c.Cmetric a.metricReference c.Theta p.budget p.epsilon p.eta
      (p.smoothingCost_nonneg a m d N 440) c.map_nonneg c.metric_nonneg a.metricReference_nonneg
      c.theta_pos p.budget_pos p.epsilon_pos p.eta_pos)
    (div_pos (p.geometryCap_pos a m d N 440) (by norm_num))

def canonicalInitialScale (C2 C442 : ℝ) : ℝ :=
  repairEntranceScale p.budget p.epsilon
    (p.canonicalEntry.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) a)
    (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442)

def canonicalTargetRadius (C2 C442 : ℝ) : ℝ :=
  repairEntranceMetricRadius
    (p.canonicalInitialScale.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) a C2 C442)
    p.budget p.eta

theorem canonicalInitialScale_and_radius_pos (C2 C442 : ℝ) (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442)
    (hPaid : repairEntranceLowFromMap (m+1) d N C2+p.epsilon/4 ≤ p.budget/4) :
    0 < p.canonicalInitialScale.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) a C2 C442 ∧
    0 < p.canonicalTargetRadius.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) a C2 C442 := by
  have hScale : 0 < p.canonicalInitialScale.{uM,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) a C2 C442 :=
    repairEntranceScale_pos p.epsilon_pos (p.canonicalEntry_pos a)
      (repairEntranceLowFromMap_nonneg _ _ _ hC2) (repairEntranceHighFromMap_nonneg _ _ _ hC442)
      (by have := p.epsilon_pos; linarith)
  exact ⟨hScale,repairEntranceMetricRadius_pos hScale p.budget_pos p.eta_pos⟩

end RepairEntranceParameters
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairEntranceParameters.canonicalCost_identity
#print axioms GlobalEmbedding.Continuation.RepairEntranceParameters.canonicalEntry_pos
#print axioms GlobalEmbedding.Continuation.RepairEntranceParameters.canonicalInitialScale_and_radius_pos
