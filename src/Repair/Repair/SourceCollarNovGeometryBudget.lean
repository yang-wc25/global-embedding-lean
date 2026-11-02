import Repair.SourceCollarNovSetupSmoothing
import Repair.EndpointOriginalNumericalSetup

/-!
# Fixed numerical class for the unchanged original buffered Setup

The numerical setup is fixed before the atlas.  The fields below compare
only primitive input budgets with that numerical setup.  The auxiliary raw
functions have already been constructed from the original raw preparations;
enlarging their budgets changes no function, chart, support or norm domain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

structure SourceCollarNovGeometryBounds
    (c : RepairOriginalNumericalSetup m d N) (g : SourceCollarNovSetup (m+1) d M P) : Prop where
  BS : ∀ j, sourceCollarNovParentRawProfile g.BS j ≤ c.BS j
  TS : ∀ j, g.TS j ≤ c.TS j
  BP : ∀ j, sourceCollarNovParentRawProfile g.BP j ≤ c.BP j
  TP : ∀ j, g.TP j ≤ c.TP j
  Ds : g.Ds ≤ c.Ds
  Dp : g.Dp ≤ c.Dp
  parameterTransition : ∀ j, g.parameterTransition j ≤ c.parameterTransition j
  spatialTransition : ∀ j, g.spatialTransition j ≤ c.spatialTransition j
  sourceBound : g.coordinateRadius ≤ c.sourceBound
  parameterBound : g.coordinateRadius ≤ c.parameterBound
  modelRadius : g.coordinateRadius ≤ c.referenceBudget.modelRadius
  buffer : c.referenceBudget.buffer ≤ g.parentRadius
  smoothingRadius : c.smoothingRadius ≤ min g.parameter.buffer g.source.buffer

namespace SourceCollarNovGeometryBounds
variable {c : RepairOriginalNumericalSetup m d N} {g : SourceCollarNovSetup (m+1) d M P}
  (h : SourceCollarNovGeometryBounds c g)

def sourcePreparation : TensorRawCutoffPreparation g.source c.BS c.TS c.Ds where
  raw := g.sourceParentPreparation.raw
  smooth := g.sourceParentPreparation.smooth
  plateau_cover := g.sourceParentPreparation.plateau_cover
  inner_support := g.sourceParentPreparation.inner_support
  enlarged_support := g.sourceParentPreparation.enlarged_support
  degree := g.sourceParentPreparation.degree.trans h.Ds
  own_jets := fun i j y hy => (g.sourceParentPreparation.own_jets i j y hy).trans (h.BS j)
  transition_jets := fun i k j hj y hy ha =>
    (g.sourceParentPreparation.transition_jets i k j hj y hy ha).trans (h.TS j)

def parameterPreparation : TensorRawCutoffPreparation g.parameter c.BP c.TP c.Dp where
  raw := g.parameterParentPreparation.raw
  smooth := g.parameterParentPreparation.smooth
  plateau_cover := g.parameterParentPreparation.plateau_cover
  inner_support := g.parameterParentPreparation.inner_support
  enlarged_support := g.parameterParentPreparation.enlarged_support
  degree := g.parameterParentPreparation.degree.trans h.Dp
  own_jets := fun i j y hy => (g.parameterParentPreparation.own_jets i j y hy).trans (h.BP j)
  transition_jets := fun i k j hj y hy ha =>
    (g.parameterParentPreparation.transition_jets i k j hj y hy ha).trans (h.TP j)

def parameterLocalPreparation : TensorLocalRawPreparation g.parameterFamily univ c.BP c.TP c.Dp :=
  parameterRound2_localPreparationOfGlobal g.parameter h.parameterPreparation univ

/-- Budget normalization retains all computational data exactly. -/
theorem preparation_original_fields :
    h.sourcePreparation.raw = g.sourceParentPreparation.raw ∧
    h.parameterPreparation.raw = g.parameterParentPreparation.raw ∧
    h.parameterLocalPreparation.raw = g.parameterLocalPreparation.raw ∧
    h.parameterLocalPreparation.enlarged = g.parameter.support :=
  ⟨rfl,rfl,rfl,rfl⟩

include h in
/-- The same literal outer/theta have the fixed class's numerical profiles. -/
theorem parents : RepairReferenceOriginalParentProperties g.source g.parameterFamily
    g.source.support g.parameter.support g.outer g.theta c.outerProfile c.parentProfile
    (fun j => max (c.TP j) (c.TS j)) c.Ds c.Dp :=
  repair_reference_original_product_parents c.BS c.TS c.BP c.TP
    c.BS_nonneg c.TS_nonneg c.BP_nonneg c.TP_nonneg c.Ds c.Dp
    g.source g.parameterFamily g.source_smooth g.parameter_smooth.chart_mem
    h.sourcePreparation h.parameterLocalPreparation g.Omega g.Q
    g.source_compact g.parameter_compact g.source_target g.parameter_target
    g.source_sampling g.parameter_local_sampling

include h in
theorem parent_buffer (i) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
    (hz : z ∈ g.parentCarrier i) : ball z c.referenceBudget.buffer ⊆ g.parentDomain i :=
  g.parent_buffer c.referenceBudget.buffer h.buffer i z hz

include h in
theorem parentCarrier_bound (i) :
    g.parentCarrier i ⊆ closedBall 0 c.referenceBudget.modelRadius :=
  (g.parentCarrier_bound i).trans (closedBall_subset_closedBall h.modelRadius)

/-- This record contains the actual prepared raw functions and the literal
original geometry, with only their numerical budgets enlarged. -/
def smoothingGeometry (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hAtlas : Data.atlas = g.source) (hCount : Data.parameterCount = g.parameter.count)
    (hChart : HEq Data.parameterChart g.parameter.chart)
    (hOmega : HEq Data.sourceNormDomain g.Omega)
    (hQ : HEq Data.parameterNormDomain g.Q) (hSet : Data.parameterSet = univ) :
    RepairOriginalSmoothingGeometry Data c.BS c.TS c.BP c.TP c.Ds c.Dp c.smoothingRadius := by
  rcases Data with ⟨A,Omega,pcount,chart,Q,K,W,F,H,H0,pc,phase,cutoff,normal,domain,argument,neighborhood⟩
  dsimp only at hAtlas hCount hChart hOmega hQ hSet
  subst A
  subst pcount
  have hChart' := eq_of_heq hChart
  have hOmega' := eq_of_heq hOmega
  have hQ' := eq_of_heq hQ
  subst chart
  subst Omega
  subst Q
  subst K
  exact {
    parameterFamily := g.parameterFamily
    chart_eq := rfl
    sourcePreparation := h.sourcePreparation
    parameterPreparation := h.parameterLocalPreparation
    buffer := h.smoothingRadius
    source_compact := g.source_compact
    parameter_compact := g.parameter_compact
    source_sampling := g.source_sampling
    parameter_sampling := g.parameter_local_sampling }

end SourceCollarNovGeometryBounds
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.SourceCollarNovGeometryBounds.preparation_original_fields
#print axioms GlobalEmbedding.Continuation.SourceCollarNovGeometryBounds.parents
#print axioms GlobalEmbedding.Continuation.SourceCollarNovGeometryBounds.smoothingGeometry
