import Repair.SourceCollarNovSetupParents
import Repair.EndpointSmoothingGeometry

/-! Actual old smoothing geometry for native data with the unchanged
original fixed atlas, charts, norm domains and parameter set.  The equality
arguments only identify these literal fields; they carry no analytic output
estimate.  The raw preparations and every geometric field are constructed
from SourceCollarNovSetup. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

namespace SourceCollarNovSetup
variable (g : SourceCollarNovSetup n d M P)

theorem parentRadius_le_buffer : g.parentRadius ≤ min g.parameter.buffer g.source.buffer := by
  apply le_min
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_left _ _)

/-- The existing smoothing record, produced with the actual auxiliary raw
preparations.  The original atlas, Omega, Q and norms are preserved literally. -/
def smoothingGeometry (Data : IncrementsOriginalNativeData n d N M P)
    (hAtlas : Data.atlas = g.source) (hCount : Data.parameterCount = g.parameter.count)
    (hChart : HEq Data.parameterChart g.parameter.chart)
    (hOmega : HEq Data.sourceNormDomain g.Omega)
    (hQ : HEq Data.parameterNormDomain g.Q) (hSet : Data.parameterSet = univ)
    (radius : ℝ) (hRadius : radius ≤ min g.parameter.buffer g.source.buffer) :
    RepairOriginalSmoothingGeometry Data (sourceCollarNovParentRawProfile g.BS) g.TS
      (sourceCollarNovParentRawProfile g.BP) g.TP g.Ds g.Dp radius := by
  rcases Data with ⟨A,Omega,c,chart,Q,K,W,F,H,H0,pc,phase,cutoff,normal,domain,argument,neighborhood⟩
  dsimp only at hAtlas hCount hChart hOmega hQ hSet
  subst A
  subst c
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
    sourcePreparation := g.sourceParentPreparation
    parameterPreparation := g.parameterLocalPreparation
    buffer := hRadius
    source_compact := g.source_compact
    parameter_compact := g.parameter_compact
    source_sampling := g.source_sampling
    parameter_sampling := g.parameter_local_sampling }

/-- The constructed parent collar radius also pays the original smoothing
buffer; no second geometric radius or collar premise is needed. -/
def smoothingGeometryFromParentRadius (Data : IncrementsOriginalNativeData n d N M P)
    (hAtlas : Data.atlas = g.source) (hCount : Data.parameterCount = g.parameter.count)
    (hChart : HEq Data.parameterChart g.parameter.chart)
    (hOmega : HEq Data.sourceNormDomain g.Omega)
    (hQ : HEq Data.parameterNormDomain g.Q) (hSet : Data.parameterSet = univ)
    (radius : ℝ) (hRadius : radius ≤ g.parentRadius) :
    RepairOriginalSmoothingGeometry Data (sourceCollarNovParentRawProfile g.BS) g.TS
      (sourceCollarNovParentRawProfile g.BP) g.TP g.Ds g.Dp radius :=
  g.smoothingGeometry Data hAtlas hCount hChart hOmega hQ hSet radius
    (hRadius.trans g.parentRadius_le_buffer)

end SourceCollarNovSetup
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.smoothingGeometry
#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.smoothingGeometryFromParentRadius
