import Repair.SourceCollarNovSetup
import Repair.ReferenceOriginalParentsCarrier

/-! The literal old product-parent formulas, now fed by the actual auxiliary
raw preparations. Their carriers have the proved original-chart collars,
while all graph supports, norm domains and transition profiles are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

namespace SourceCollarNovSetup
variable (g : SourceCollarNovSetup n d M P)

def outer : (Fin g.source.count × Fin g.parameter.count) → P × M → ℝ :=
  parameterLocalProductCutoff g.source g.parameterFamily
    (squareNormalizedCutoff g.sourceParentPreparation.raw)
    (tensorLocalNormalizedCutoff g.parameterLocalPreparation.raw)

def theta : (Fin g.source.count × Fin g.parameter.count) → P × M → ℝ :=
  round3ParameterProductParent g.source g.parameterFamily
    (squareNormalizedCutoff g.sourceParentPreparation.raw)
    (tensorLocalNormalizedCutoff g.parameterLocalPreparation.raw)

def outerProfile : ℕ → ℝ :=
  round4ProductCutoffProfile (sourceCollarNovParentRawProfile g.BS) g.TS
    (sourceCollarNovParentRawProfile g.BP) g.TP g.Ds g.Dp

def parentProfile : ℕ → ℝ :=
  round4ParentProfile (sourceCollarNovParentRawProfile g.BS) g.TS
    (sourceCollarNovParentRawProfile g.BP) g.TP g.Ds g.Dp

theorem outerProfile_nonneg (j : ℕ) : 0 ≤ g.outerProfile j :=
  round4ProductCutoffProfile_nonneg g.sourceParentProfile_nonneg g.TS_nonneg
    g.parameterParentProfile_nonneg g.TP_nonneg g.Ds g.Dp j

theorem parentProfile_nonneg (j : ℕ) : 0 ≤ g.parentProfile j :=
  round4ParentProfile_nonneg g.sourceParentProfile_nonneg g.TS_nonneg
    g.parameterParentProfile_nonneg g.TP_nonneg g.Ds g.Dp j

/-- Exact equality with the previously constructed actual parent product. -/
theorem outer_eq_parentProduct :
    g.outer = sourceCollarNovParentProduct g.sourcePreparation g.parameterPreparation := by
  funext i z
  change tensorLocalNormalizedCutoff g.parameterParentPreparation.raw i.2 z.1 *
      squareNormalizedCutoff g.sourceParentPreparation.raw i.1 z.2 = _
  unfold sourceParentPreparation
  rw [← sourceCollarNovParent_original_square_formula g.source_smooth
    g.sourcePreparation g.BS_nonneg]
  rfl

theorem theta_eq_square (i) (z : P × M) : g.theta i z = g.outer i z ^ 2 := by
  rw [pow_two]
  rfl

theorem parents : RepairReferenceOriginalParentProperties g.source g.parameterFamily
    g.source.support g.parameter.support g.outer g.theta g.outerProfile g.parentProfile
    (fun j => max (g.TP j) (g.TS j)) g.Ds g.Dp :=
  repair_reference_original_product_parents
    (sourceCollarNovParentRawProfile g.BS) g.TS (sourceCollarNovParentRawProfile g.BP) g.TP
    g.sourceParentProfile_nonneg g.TS_nonneg g.parameterParentProfile_nonneg g.TP_nonneg
    g.Ds g.Dp g.source g.parameterFamily g.source_smooth g.parameter_smooth.chart_mem
    g.sourceParentPreparation g.parameterLocalPreparation g.Omega g.Q
    g.source_compact g.parameter_compact g.source_target g.parameter_target
    g.source_sampling g.parameter_local_sampling

def parentDomain (i : Fin g.source.count × Fin g.parameter.count) : Set X :=
  sourceCollarNovParentProductDomain g.sourcePreparation g.parameterPreparation i

def parentCarrier (i : Fin g.source.count × Fin g.parameter.count) : Set X :=
  sourceCollarNovParentProductCarrier g.sourcePreparation g.parameterPreparation i

def parentRadius : ℝ := min (sourceCollarNovParentRadius g.source g.BS)
  (sourceCollarNovParentRadius g.parameter g.BP)

theorem parentRadius_pos : 0 < g.parentRadius :=
  lt_min (sourceCollarNovParentRadius_pos g.source g.BS (g.BS_nonneg 1))
    (sourceCollarNovParentRadius_pos g.parameter g.BP (g.BP_nonneg 1))

theorem parentDomain_open (i) : IsOpen (g.parentDomain i) :=
  sourceCollarNovParentProduct_domain_open g.sourcePreparation g.parameterPreparation i

theorem parentDomain_original (i) : g.parentDomain i ⊆ sourceCollarNovOriginalOuter g.source g.parameter i :=
  sourceCollarNovParentProduct_domain_original g.sourcePreparation g.parameterPreparation i

theorem parentDomain_inner (i) (z : X) (hz : z ∈ g.parentDomain i) :
    (g.parameter.chart i.2).symm z.1 ∈ g.parameter.inner i.2 ∧
      (g.source.chart i.1).symm z.2 ∈ g.source.inner i.1 :=
  sourceCollarNovParentProduct_domain_inner g.sourcePreparation g.parameterPreparation i z hz

theorem parentDomain_sample (i) (z : X) (hz : z ∈ g.parentDomain i) :
    parameterTensorModelEquiv n d z ∈ g.samples i :=
  sourceCollarNov_original_samples g.source g.parameter g.Omega g.Q
    g.source_sampling g.parameter_sampling i z (g.parentDomain_original i hz)

theorem parent_buffer (r : ℝ) (hr : r ≤ g.parentRadius) (i) (z : X)
    (hz : z ∈ g.parentCarrier i) : ball z r ⊆ g.parentDomain i :=
  sourceCollarNovParentProduct_buffer g.sourcePreparation g.parameterPreparation
    g.source_smooth g.parameter_smooth (g.BS_nonneg 1) (g.BP_nonneg 1) r
    (hr.trans (min_le_left _ _)) (hr.trans (min_le_right _ _)) i z hz

theorem parentCarrier_subset_domain (i) : g.parentCarrier i ⊆ g.parentDomain i := by
  intro z hz
  exact g.parent_buffer g.parentRadius le_rfl i z hz (mem_ball_self g.parentRadius_pos)

theorem parentCarrier_sample (i) (z : X) (hz : z ∈ g.parentCarrier i) :
    parameterTensorModelEquiv n d z ∈ g.samples i :=
  g.parentDomain_sample i z (g.parentCarrier_subset_domain i hz)

theorem parentCarrier_original (i) :
    g.parentCarrier i ⊆ sourceCollarNovOriginalInner g.source g.parameter i :=
  sourceCollarNovParentProduct_carrier_original g.sourcePreparation g.parameterPreparation i

theorem parentCarrier_bound (i) : g.parentCarrier i ⊆ closedBall 0 g.coordinateRadius :=
  (g.parentCarrier_original i).trans (sourceCollarNov_original_inner_bounded
    g.source g.parameter g.Omega g.Q g.source_sampling g.parameter_sampling
    g.coordinateRadius g.source_bound g.parameter_bound i)

theorem parentCarrier_compact [T2Space M] [T2Space P] (i) : IsCompact (g.parentCarrier i) :=
  (sourceCollarNovParent_carrier_compact g.parameterPreparation g.Q
    g.parameter_compact g.parameter_target g.parameter_sampling i.2).prod
      (sourceCollarNovParent_carrier_compact g.sourcePreparation g.Omega
        g.source_compact g.source_target g.source_sampling i.1)

theorem outer_carrier (i) : tsupport (g.outer i) ⊆
    ((g.parameter.chart i.2).prod (g.source.chart i.1)).source ∩
      ((g.parameter.chart i.2).prod (g.source.chart i.1)) ⁻¹' g.parentCarrier i := by
  rw [g.outer_eq_parentProduct]
  exact sourceCollarNovParentProduct_source g.sourcePreparation g.parameterPreparation i

theorem theta_carrier (i) : tsupport (g.theta i) ⊆
    ((g.parameter.chart i.2).prod (g.source.chart i.1)).source ∩
      ((g.parameter.chart i.2).prod (g.source.chart i.1)) ⁻¹' g.parentCarrier i :=
  (g.parents.theta_subset_outer i).trans (g.outer_carrier i)

end SourceCollarNovSetup
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.parents
#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.parent_buffer
#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.outer_carrier
