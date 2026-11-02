import Repair.EndpointOriginalNumericalSetup
import Repair.EntranceCanonicalFinitePlan

/-! The complete finite entrance has no source or parameter manifold value
as an argument. The universe parameters merely bound the types quantified
over by the actual uniform Euclidean estimates. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
namespace GlobalEmbedding.Continuation
namespace RepairOriginalNumericalSetup
universe uM uP
variable {m d N : ℕ} (c : RepairOriginalNumericalSetup m d N)

def canonicalInitialScale (rho : ℝ) (hrho : 0 < rho) : ℝ :=
  (c.parameters rho hrho).canonicalInitialScale.{uM,uP,0,0,0}
    (m := m) (d := d) (N := N) c.plan (c.mapBounds 2) (c.mapBounds 442)

def canonicalMetricRadius (rho : ℝ) (hrho : 0 < rho) : ℝ :=
  (c.parameters rho hrho).canonicalTargetRadius.{uM,uP,0,0,0}
    (m := m) (d := d) (N := N) c.plan (c.mapBounds 2) (c.mapBounds 442)

theorem canonical_initialScale_metricRadius_pos (rho : ℝ) (hrho : 0 < rho) :
    0 < c.canonicalInitialScale.{uM,uP} rho hrho ∧
      0 < c.canonicalMetricRadius.{uM,uP} rho hrho :=
  (c.parameters rho hrho).canonicalInitialScale_and_radius_pos c.plan
    (c.mapBounds 2) (c.mapBounds 442) (c.mapBounds_nonneg 2)
    (c.mapBounds_nonneg 442) (c.parameters_paid rho hrho)

theorem canonical_initialScale_lt_one (rho : ℝ) (hrho : 0 < rho) :
    c.canonicalInitialScale.{uM,uP} rho hrho < 1 := by
  have h : c.canonicalInitialScale.{uM,uP} rho hrho ≤ (1/2 : ℝ) :=
    repairEntranceScale_le_half _ _ _ _ _
  exact h.trans_lt (by norm_num)

end RepairOriginalNumericalSetup
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairOriginalNumericalSetup.canonical_initialScale_metricRadius_pos
