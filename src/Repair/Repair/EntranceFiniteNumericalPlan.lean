import Repair.EntranceNamedNumericalCosts
import Repair.EntranceEnvelopeScale
import Repair.EntranceFromMapBounds
import Probes.Round4ParameterSecondaryScalePrefix

/-!
# The numerical entrance is selected before a reference map

All fields are numerical bounds from the fixed setup. No field contains a
map, atlas, constructed increment, initial state, or trajectory. The
selected cost is the actual named mean/secondary formula, and the entry
and original C440 error radius are positive functions of these numbers.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

structure RepairEntranceProfiles where
  BS : ℕ → ℝ
  TS : ℕ → ℝ
  BP : ℕ → ℝ
  TP : ℕ → ℝ
  Inverse : ℕ → ℝ
  Forward : ℕ → ℝ
  Given : ℕ → ℝ
  reference : ℕ → ℝ
  metricReference : ℕ → ℝ
  Meta : ℕ → ℝ
  Kcut : ℕ → ℝ
  Tinv : ℕ → ℝ
  Tobs : ℕ → ℝ
  BS_nonneg : ∀ j, 0 ≤ BS j
  TS_nonneg : ∀ j, 0 ≤ TS j
  BP_nonneg : ∀ j, 0 ≤ BP j
  TP_nonneg : ∀ j, 0 ≤ TP j
  reference_nonneg : ∀ j, 0 ≤ reference j
  metricReference_nonneg : ∀ j, 0 ≤ metricReference j

structure RepairEntranceParameters where
  radius : ℝ
  radius_pos : 0 < radius
  Ds : ℕ
  Dp : ℕ
  Rsub : ℕ
  Lprimary : ℕ
  Rsecondary : ℕ
  budget : ℝ
  epsilon : ℝ
  eta : ℝ
  budget_pos : 0 < budget
  epsilon_pos : 0 < epsilon
  eta_pos : 0 < eta
  normalF : ℝ
  normalT : ℝ
  c : ℝ
  cT : ℝ
  secondaryReserve : ℝ
  meanReserve : ℝ
  meanReserve_pos : 0 < meanReserve
  geometryTolerance : ℝ
  linearBound : ℝ
  reserve : ℝ
  geometryTolerance_pos : 0 < geometryTolerance
  linearBound_nonneg : 0 ≤ linearBound
  reserve_pos : 0 < reserve

namespace RepairEntranceParameters
variable (p : RepairEntranceParameters) (a : RepairEntranceProfiles)

def smoothingCost (m d q j : ℕ) : ℝ :=
  round4PreparedPairConstant (m+1) d p.radius p.radius_pos a.BS a.TS a.BP a.TP p.Ds p.Dp j q

theorem smoothingCost_nonneg (m d N q j : ℕ) : 0 ≤ p.smoothingCost a m d q j :=
  (round4_actual_local_set_pair_smoothing
    (n := m+1) (d := d) (N := N)
    (M := EuclideanSpace ℝ (Fin (m+1))) (P := EuclideanSpace ℝ (Fin d))
    a.BS a.TS a.BP a.TP a.BS_nonneg a.TS_nonneg a.BP_nonneg a.TP_nonneg
    p.Ds p.Dp p.radius p.radius_pos j q).1

def packet (m d N q : ℕ) : ℕ → ℝ :=
  round4ParameterStageInputProfile m d N p.radius p.radius_pos a.BS a.TS a.BP a.TP
    a.Inverse a.Forward a.Given a.reference p.Ds p.Dp q p.budget p.normalF p.normalT

theorem packet_nonneg (m d N q j : ℕ) : 0 ≤ p.packet a m d N q j :=
  (mul_nonneg (p.smoothingCost_nonneg a m d N q j) p.budget_pos.le).trans (le_max_left _ _)

def targetBudget (m d N q : ℕ) : ℕ → ℝ :=
  round4ParameterRepairReferenceProfile (m+1) d N p.radius p.radius_pos
    a.BS a.TS a.BP a.TP p.Ds p.Dp q a.metricReference p.budget

def secondaryGeometry (m d N q : ℕ) : ℕ → ℝ :=
  round4ParameterSecondaryGeometryProfile m d N q (fun _ : Unit => p.secondaryReserve)
    (p.packet a m d N q) a.Tinv a.Tobs p.c

def cutoff (q : ℕ) (j : ℕ) : ℝ := a.Kcut (actualSecondarySolveOrder q j)

universe uM uP uΛ uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def completedProfile (q : ℕ) (hq : 1 ≤ q) : Round3RepairPrimitiveProfiles :=
  round4ParameterCarrierCompletedProfile.{uM,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M)
    (p.targetBudget a m d N q) q p.Rsub p.Lprimary p.Rsecondary hq
    p.meanReserve p.meanReserve_pos p.c p.cT
    (p.packet a m d N q) a.Forward a.Inverse a.Meta (p.packet_nonneg a m d N q)
    (p.secondaryGeometry a m d N q) (cutoff a q) a.Tinv a.Tobs

def cost (q : ℕ) (hq : 1 ≤ q) : Round3RepairPrimitiveCosts :=
  repairEntranceNumericCosts.{uM,uP,0,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
    (p.targetBudget a m d N q) q hq
    (p.completedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) a q hq)

theorem cost_identity (q : ℕ) (hq : 1 ≤ q) :
    Round4ParameterRepairCostIdentity.{uM,uP,0,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      (p.targetBudget a m d N q) q hq
      (p.completedProfile.{uM,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) a q hq)
      (p.cost.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) a q hq) :=
  repairEntranceNumericCosts_identity _ _ _ _

def geometryCap (m d q : ℕ) : ℝ :=
  round3RepairComputedGeometryThreshold (2*p.smoothingCost a m d q 0)
    p.budget (a.reference 0) p.linearBound p.reserve p.geometryTolerance

theorem geometryCap_pos (m d N q : ℕ) : 0 < p.geometryCap a m d q :=
  round3RepairComputedGeometryThreshold_pos _ _ _ _ _ _
    (mul_nonneg (by norm_num) (p.smoothingCost_nonneg a m d N q 0))
    p.budget_pos.le (a.reference_nonneg 0) p.linearBound_nonneg p.reserve_pos p.geometryTolerance_pos

def entry : ℝ :=
  let c := p.cost.{uM,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) a 440 (by norm_num)
  min (round4ParameterNumericalBlockScale m d N (p.smoothingCost a m d 440)
    c.Cmap c.Cmetric a.metricReference c.Theta p.budget p.epsilon p.eta 10)
    (p.geometryCap a m d 440/2)

theorem entry_pos :
    0 < p.entry.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) a := by
  let c := p.cost.{uM,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) a 440 (by norm_num)
  exact lt_min
    (repairEntrance_numerical_scale_positive m d N 10 (p.smoothingCost a m d 440)
      c.Cmap c.Cmetric a.metricReference c.Theta p.budget p.epsilon p.eta
      (p.smoothingCost_nonneg a m d N 440) c.map_nonneg c.metric_nonneg a.metricReference_nonneg
      c.theta_pos p.budget_pos p.epsilon_pos p.eta_pos)
    (div_pos (p.geometryCap_pos a m d N 440) (by norm_num))

def initialScale (C2 C442 : ℝ) : ℝ :=
  repairEntranceScale p.budget p.epsilon
    (p.entry.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) a)
    (repairEntranceLowFromMap (m+1) d N C2) (repairEntranceHighFromMap (m+1) d N C442)

def targetRadius (C2 C442 : ℝ) : ℝ :=
  repairEntranceMetricRadius
    (p.initialScale.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) a C2 C442)
    p.budget p.eta

theorem initialScale_and_radius_pos (C2 C442 : ℝ) (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442)
    (hPaid : repairEntranceLowFromMap (m+1) d N C2+p.epsilon/4 ≤ p.budget/4) :
    0 < p.initialScale.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) a C2 C442 ∧
    0 < p.targetRadius.{uM,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) a C2 C442 := by
  have hScale : 0 < p.initialScale.{uM,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) a C2 C442 :=
    repairEntranceScale_pos p.epsilon_pos (p.entry_pos a)
      (repairEntranceLowFromMap_nonneg _ _ _ hC2) (repairEntranceHighFromMap_nonneg _ _ _ hC442)
      (by have := p.epsilon_pos; linarith)
  exact ⟨hScale,repairEntranceMetricRadius_pos hScale p.budget_pos p.eta_pos⟩

end RepairEntranceParameters
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairEntranceParameters.cost_identity
#print axioms GlobalEmbedding.Continuation.RepairEntranceParameters.entry_pos
#print axioms GlobalEmbedding.Continuation.RepairEntranceParameters.initialScale_and_radius_pos
