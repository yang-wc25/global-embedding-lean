import Repair.EntranceFactoryNumericalPlan
import Repair.EndpointFixedReferenceProfile
import Repair.EntranceFiniteReferenceEnvelope
import Repair.EntranceOriginalGivenMapTensor
import Repair.ReferenceOriginalLocalFactoryPositive

/-! The original uniform numerical class. Its complete finite entrance
is fixed before any atlas, reference map, metric or generated phase family.
The allowed map is constrained only through the separately displayed J*. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

structure RepairOriginalNumericalSetup (m d N : ℕ) where
  referenceBudget : RepairReferenceFactoryBudget m d N
  mapBounds : ℕ → ℝ
  mapBounds_nonneg : ∀ j, 0 ≤ mapBounds j
  BS : ℕ → ℝ
  TS : ℕ → ℝ
  BP : ℕ → ℝ
  TP : ℕ → ℝ
  parameterTransition : ℕ → ℝ
  spatialTransition : ℕ → ℝ
  BS_nonneg : ∀ j, 0 ≤ BS j
  TS_nonneg : ∀ j, 0 ≤ TS j
  BP_nonneg : ∀ j, 0 ≤ BP j
  TP_nonneg : ∀ j, 0 ≤ TP j
  parameter_nonneg : ∀ j, 0 ≤ parameterTransition j
  spatial_nonneg : ∀ j, 0 ≤ spatialTransition j
  Ds : ℕ
  Dp : ℕ
  transition : ℝ
  centerBound : ℝ
  parameterBound : ℝ
  sourceBound : ℝ
  lower : ℝ
  smoothingRadius : ℝ
  transition_pos : 0 < transition
  centerBound_nonneg : 0 ≤ centerBound
  parameterBound_nonneg : 0 ≤ parameterBound
  sourceBound_nonneg : 0 ≤ sourceBound
  lower_pos : 0 < lower
  smoothingRadius_pos : 0 < smoothingRadius
  modelRadius_nonneg : 0 ≤ referenceBudget.modelRadius
  spatial_first : spatialTransition 1 ≤ transition
  mapC3 : mapBounds 3 ≤ referenceBudget.mapC3
  tensorC1 : repairEntranceMetricCost (m+1) d N 1*(mapBounds 3)^2 ≤ referenceBudget.tensorC1
  first_lower : referenceBudget.firstLower ≤ lower
  tensor_lower : referenceBudget.tensorLower ≤ lower

namespace RepairOriginalNumericalSetup
variable {m d N : ℕ} (c : RepairOriginalNumericalSetup m d N)

def labelBound : ℕ := ((c.Ds+2)*(c.Dp+2))*(c.referenceBudget.pieceBound*
  Fintype.card (EdgePair (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1)))+1)))

def cap : ℝ := repairEntranceFactoryWeightCap c.referenceBudget c.transition c.labelBound

def rawReserve : ℝ := repairReferenceFactoryPositiveReserve c.referenceBudget

def reserve : ℝ := c.rawReserve/c.cap^2

theorem cap_pos : 0 < c.cap :=
  zero_lt_one.trans_le (repairEntranceFactoryWeightCap_one_le c.referenceBudget c.transition c.transition_pos c.labelBound)

theorem reserve_pos : 0 < c.reserve :=
  div_pos (repair_reference_factory_positive_reserve_pos c.referenceBudget) (sq_pos_of_pos c.cap_pos)

def outerProfile : ℕ → ℝ := round4ProductCutoffProfile c.BS c.TS c.BP c.TP c.Ds c.Dp

def parentProfile : ℕ → ℝ := round4ParentProfile c.BS c.TS c.BP c.TP c.Ds c.Dp

def givenProfile : ℕ → ℝ := repairReferenceOriginalFixedProfile c.referenceBudget c.cap c.sourceBound
  c.mapBounds c.outerProfile c.parameterTransition c.spatialTransition

def referenceProfile : ℕ → ℝ := repairEntranceAllowedMetricProfile (m+1) d N c.mapBounds

theorem outerProfile_nonneg (j : ℕ) : 0 ≤ c.outerProfile j :=
  round4ProductCutoffProfile_nonneg c.BS_nonneg c.TS_nonneg c.BP_nonneg c.TP_nonneg c.Ds c.Dp j

theorem parentProfile_nonneg (j : ℕ) : 0 ≤ c.parentProfile j :=
  round4ParentProfile_nonneg c.BS_nonneg c.TS_nonneg c.BP_nonneg c.TP_nonneg c.Ds c.Dp j

theorem referenceProfile_nonneg (j : ℕ) : 0 ≤ c.referenceProfile j :=
  repairEntranceAllowedMetricProfile_nonneg (m+1) d N c.mapBounds j

def plan : RepairEntranceProfiles := repairEntranceFactoryProfiles c.referenceBudget
  c.transition c.centerBound c.parameterBound c.sourceBound c.labelBound c.Ds c.Dp
  c.BS c.TS c.BP c.TP c.parentProfile c.parameterTransition c.spatialTransition
  c.givenProfile c.referenceProfile c.referenceProfile
  c.BS_nonneg c.TS_nonneg c.BP_nonneg c.TP_nonneg c.referenceProfile_nonneg c.referenceProfile_nonneg

def parameters (rho : ℝ) (hrho : 0 < rho) : RepairEntranceParameters :=
  repairEntranceFactoryParameters c.referenceBudget c.transition c.centerBound c.parameterBound
    c.sourceBound c.lower c.reserve (c.mapBounds 2) (c.givenProfile 0) rho
    c.labelBound c.Ds c.Dp c.labelBound c.smoothingRadius c.smoothingRadius_pos
    c.parameterTransition c.spatialTransition c.transition_pos c.centerBound_nonneg
    c.parameterBound_nonneg c.sourceBound_nonneg c.modelRadius_nonneg c.lower_pos c.reserve_pos
    (c.mapBounds_nonneg 2) hrho c.parameter_nonneg c.spatial_nonneg

theorem parameters_epsilon_le_one (rho : ℝ) (hrho : 0 < rho) : (c.parameters rho hrho).epsilon ≤ 1 :=
  min_le_left _ _

theorem parameters_paid (rho : ℝ) (hrho : 0 < rho) :
    repairEntranceLowFromMap (m+1) d N (c.mapBounds 2)+(c.parameters rho hrho).epsilon/4 ≤
      (c.parameters rho hrho).budget/4 := by
  change repairEntranceLowFromMap (m+1) d N (c.mapBounds 2)+(c.parameters rho hrho).epsilon/4 ≤
    (4*(repairEntranceLowFromMap (m+1) d N (c.mapBounds 2)+1))/4
  have := c.parameters_epsilon_le_one rho hrho
  linarith

universe uM uP
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def initialScale (rho : ℝ) (hrho : 0 < rho) : ℝ :=
  (c.parameters rho hrho).initialScale.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M)
    c.plan (c.mapBounds 2) (c.mapBounds 442)

def metricRadius (rho : ℝ) (hrho : 0 < rho) : ℝ :=
  (c.parameters rho hrho).targetRadius.{uM,uP,0,0,0} (m := m) (d := d) (N := N) (M := M)
    c.plan (c.mapBounds 2) (c.mapBounds 442)

theorem initialScale_metricRadius_pos (rho : ℝ) (hrho : 0 < rho) :
    0 < c.initialScale.{uM,uP} (M := M) rho hrho ∧ 0 < c.metricRadius.{uM,uP} (M := M) rho hrho :=
  (c.parameters rho hrho).initialScale_and_radius_pos c.plan (c.mapBounds 2) (c.mapBounds 442)
    (c.mapBounds_nonneg 2) (c.mapBounds_nonneg 442) (c.parameters_paid rho hrho)

end RepairOriginalNumericalSetup
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairOriginalNumericalSetup.initialScale_metricRadius_pos
#print axioms GlobalEmbedding.Continuation.repairEntranceOriginalMapDepth_exact
