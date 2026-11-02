import Repair.EntranceFinitePlanAttachment
import Repair.EntranceCanonicalFinitePlan
import Repair.EntranceCanonicalSecondaryScalePrefix

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem repairEntranceCanonical_plan_entry_of_finite_prefix
    (p : RepairEntranceParameters) (a b : RepairEntranceProfiles)
    (h : a.Prefix b repairEntrancePrimitiveDepth) :
    p.canonicalEntry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) a =
      p.canonicalEntry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) b := by
  exact repairEntranceCanonical_secondary_completed_stage_scale_prefix.{uM,uP,0,0,0}
    (m := m) (d := d) (N := N) (fun _ : Unit => p.secondaryReserve)
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
    (p.canonicalCost.{uM,uP,0,0,0} (m := m) (d := d) (N := N) a 440 (by norm_num))
    (p.canonicalCost.{uM,uP,0,0,0} (m := m) (d := d) (N := N) b 440 (by norm_num))
    (p.canonicalCost_identity a 440 (by norm_num)) (p.canonicalCost_identity b 440 (by norm_num))

variable {P : Type uP} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- A fixed numerical plan is actually admissible for a reference whose
constructed profiles have its allowed finite prefix. The metric of that
reference is compared with an upper bound, never assumed equal to it. -/
theorem repairEntranceCanonical_fixed_plan_entry_le_actual_block
    (p : RepairEntranceParameters) (fixed actual : RepairEntranceProfiles)
    (hPrefix : fixed.Prefix actual repairEntrancePrimitiveDepth)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (packet : Round3RepairFixedSmoothingPacket Data actual.BS actual.TS actual.BP actual.TP
      p.Ds p.Dp p.radius p.radius_pos actual.reference actual.Given)
    (cost : Round3RepairPrimitiveCosts)
    (hCost : RepairEntranceCanonicalCostIdentity.{uM,uP,0,0,0,0}
      (m := m) (d := d) (N := N) (Tr := ℝ)
      (p.targetBudget actual m d N 440) 440 (by norm_num)
      (p.canonicalCompletedProfile.{uM,uP,0,0} (m := m) (d := d) (N := N) actual 440 (by norm_num)) cost)
    (hCurrent : packet.closedReferenceProfile 440 ≤ actual.metricReference 440)
    (hNext : packet.closedReferenceProfile 480 ≤ actual.metricReference 480) :
    p.canonicalEntry.{uM,uP,0,0,0} (m := m) (d := d) (N := N) fixed ≤
      min (round4ParameterBlockScale packet (p.smoothingCost actual m d 440) cost
        p.budget p.epsilon p.eta 10) (p.geometryCap actual m d 440/2) := by
  rw [repairEntranceCanonical_plan_entry_of_finite_prefix p fixed actual hPrefix]
  let numeric := p.canonicalCost.{uM,uP,0,0,0} (m := m) (d := d) (N := N) actual 440 (by norm_num)
  have hNumeric := p.canonicalCost_identity.{uM,uP,0,0,0}
    (m := m) (d := d) (N := N) actual 440 (by norm_num)
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
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_plan_entry_of_finite_prefix
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_fixed_plan_entry_le_actual_block
