import Repair.EntranceFiniteNumericalPlan

/-!
# A fixed finite numerical entrance attaches to the actual block

This is a lower-bound attachment, not merely congruence of two arbitrary
profiles. The actual reference metric may have a smaller norm than its
allowed envelope; its own block then has a larger available entrance.
The prototype is fixed first, the actual cost comes from the reserved
factory, and the same prototype entrance is admissible for that block.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def repairEntrancePrimitiveDepth : ℕ := 40*(10+2)+1+(440+3)*(440+4)+4

theorem repairEntrancePrimitiveDepth_value : repairEntrancePrimitiveDepth = 197177 := by norm_num [repairEntrancePrimitiveDepth]

structure RepairEntranceProfiles.Prefix (a b : RepairEntranceProfiles) (J : ℕ) : Prop where
  BS : ∀ j, j ≤ J → a.BS j = b.BS j
  TS : ∀ j, j ≤ J → a.TS j = b.TS j
  BP : ∀ j, j ≤ J → a.BP j = b.BP j
  TP : ∀ j, j ≤ J → a.TP j = b.TP j
  Inverse : ∀ j, j ≤ J → a.Inverse j = b.Inverse j
  Forward : ∀ j, j ≤ J → a.Forward j = b.Forward j
  Given : ∀ j, j ≤ J → a.Given j = b.Given j
  reference : ∀ j, j ≤ J → a.reference j = b.reference j
  metricReference : ∀ j, j ≤ J → a.metricReference j = b.metricReference j
  Meta : ∀ j, j ≤ J → a.Meta j = b.Meta j
  Kcut : ∀ j, j ≤ J → a.Kcut j = b.Kcut j
  Tinv : ∀ j, j ≤ J → a.Tinv j = b.Tinv j
  Tobs : ∀ j, j ≤ J → a.Tobs j = b.Tobs j

universe uM uP
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem repairEntrance_plan_entry_of_finite_prefix
    (p : RepairEntranceParameters) (a b : RepairEntranceProfiles)
    (h : a.Prefix b repairEntrancePrimitiveDepth) :
    p.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) a =
      p.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) b := by
  exact round4Parameter_secondary_completed_stage_scale_prefix.{uM,uP,0,0,0}
    (m := m) (d := d) (N := N) (M := M) (fun _ : Unit => p.secondaryReserve)
    p.radius p.radius_pos p.Ds p.Dp a.BS a.TS a.BP a.TP a.Inverse a.Forward
    a.Given a.reference a.metricReference a.Meta b.BS b.TS b.BP b.TP b.Inverse b.Forward
    b.Given b.reference b.metricReference b.Meta p.budget p.normalF p.normalT
    p.meanReserve p.meanReserve_pos 440 p.Rsub p.Lprimary p.Rsecondary (by norm_num) p.c p.cT
    a.Kcut a.Tinv a.Tobs b.Kcut b.Tinv b.Tobs 10
    p.epsilon p.eta p.geometryTolerance p.linearBound p.reserve
    h.BS h.TS h.BP h.TP h.Inverse h.Forward h.Given h.reference h.metricReference h.Meta
    (fun j hj => h.Kcut j (hj.trans (by decide)))
    (fun j hj => h.Tinv j (hj.trans (by decide)))
    (fun j hj => h.Tobs j (hj.trans (by decide)))
    (p.packet_nonneg a m d N 440) (p.packet_nonneg b m d N 440)
    (p.cost.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) a 440 (by norm_num))
    (p.cost.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) b 440 (by norm_num))
    (p.cost_identity a 440 (by norm_num)) (p.cost_identity b 440 (by norm_num))

variable {P : Type uP} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- A fixed numerical plan is actually admissible for a reference whose
constructed profiles have its allowed finite prefix. The metric of that
reference is compared with an upper bound, never assumed equal to it. -/
theorem repairEntrance_fixed_plan_entry_le_actual_block
    (p : RepairEntranceParameters) (fixed actual : RepairEntranceProfiles)
    (hPrefix : fixed.Prefix actual repairEntrancePrimitiveDepth)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (packet : Round3RepairFixedSmoothingPacket Data actual.BS actual.TS actual.BP actual.TP
      p.Ds p.Dp p.radius p.radius_pos actual.reference actual.Given)
    (cost : Round3RepairPrimitiveCosts)
    (hCost : Round4ParameterRepairCostIdentity.{uM,uP,0,0,0,0}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      (p.targetBudget actual m d N 440) 440 (by norm_num)
      (p.completedProfile.{uM,uP,0,0} (m := m) (d := d) (N := N) (M := M) actual 440 (by norm_num)) cost)
    (hCurrent : packet.closedReferenceProfile 440 ≤ actual.metricReference 440)
    (hNext : packet.closedReferenceProfile 480 ≤ actual.metricReference 480) :
    p.entry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) fixed ≤
      min (round4ParameterBlockScale packet (p.smoothingCost actual m d 440) cost
        p.budget p.epsilon p.eta 10) (p.geometryCap actual m d 440/2) := by
  rw [repairEntrance_plan_entry_of_finite_prefix p fixed actual hPrefix]
  let numeric := p.cost.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M) actual 440 (by norm_num)
  have hNumeric := p.cost_identity.{uM,uP,0,0,0}
    (m := m) (d := d) (N := N) (M := M) actual 440 (by norm_num)
  have hTheta : numeric.Theta = cost.Theta := hNumeric.1.trans hCost.1.symm
  have hMap : numeric.Cmap = cost.Cmap := hNumeric.2.1.trans hCost.2.1.symm
  have hMetric : numeric.Cmetric = cost.Cmetric := hNumeric.2.2.trans hCost.2.2.symm
  change min (round4ParameterNumericalBlockScale m d N (p.smoothingCost actual m d 440)
    numeric.Cmap numeric.Cmetric actual.metricReference numeric.Theta p.budget p.epsilon p.eta 10)
    (p.geometryCap actual m d 440/2) ≤ _
  rw [hTheta,hMap,hMetric]
  exact repairEntrance_envelope_scale_le_actual packet (p.smoothingCost actual m d 440)
    actual.metricReference cost p.budget p.epsilon p.eta (p.geometryCap actual m d 440) 10
    (p.smoothingCost_nonneg actual m d N 440) p.budget_pos.le hCurrent hNext

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_plan_entry_of_finite_prefix
#print axioms GlobalEmbedding.Continuation.repairEntrance_fixed_plan_entry_le_actual_block
