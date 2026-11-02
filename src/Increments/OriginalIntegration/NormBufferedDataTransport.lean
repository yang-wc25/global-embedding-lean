import FaithfulCollars.OriginalNormBufferGeometry
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs
import Probes.ActualOriginalGivenProfile
import Repair.EntranceOriginalObserverJets

/-!
# Exact original-data transport for a smaller internal norm buffer

Source: main.tex, setup:uniform and lem:increments. The manufactured working
atlas changes only inner annotations and buffer. Its chart functions, count,
original supports, original Omega/Q and all given physical fields remain
literal. Every original qualitative premise and finite-budget expression is
transported without a new analytic assumption. Unlike the prior fixed-ball
adapter, original inner sets can have arbitrary shape within their original
bounded and buffered coordinate sets.

This is transport, not a claim that the original weak bare-atlas record
already contains buffered norm-domain geometry; that input is audited and
manufactured separately.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulCollars

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

def normBufferedData (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer) :
    IncrementsOriginalNativeData n d N M P :=
  { Data with atlas := originalNormBufferedAtlas Data.atlas b hb hbuffer }

theorem normBufferedData_given_profile
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer) (j : ℕ) (ell : ℝ) :
    actualOriginalGivenInputProfile (normBufferedData Data b hb hbuffer) j ell =
      actualOriginalGivenInputProfile Data j ell := rfl


variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem normBufferedData_domain_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (hd : IncrementsOriginalDomainConditions Data) :
    IncrementsOriginalDomainConditions (normBufferedData Data b hb hbuffer) where
  source_dim := hd.source_dim
  target_dim := hd.target_dim
  parameter_open := hd.parameter_open
  parameter_compact := hd.parameter_compact
  parameter_subset := hd.parameter_subset
  atlas_smooth := ⟨hd.atlas_smooth.chart_mem, hd.atlas_smooth.support_subset⟩
  parameter_charts_smooth := hd.parameter_charts_smooth
  source_norm_subset := hd.source_norm_subset
  source_inner_norm := hd.source_inner_norm
  parameter_norm_subset := hd.parameter_norm_subset
  parameter_cover := hd.parameter_cover
  primary_open := hd.primary_open
  cutoff_support_local := hd.cutoff_support_local

theorem normBufferedData_smooth_inputs
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (hs : IncrementsOriginalSmoothInputs Data) :
    IncrementsOriginalSmoothInputs (normBufferedData Data b hb hbuffer) where
  F_joint := hs.F_joint
  H_coordinates := hs.H_coordinates
  phase_joint := hs.phase_joint
  cutoff_joint := hs.cutoff_joint
  normal_joint := hs.normal_joint

theorem normBufferedData_phase_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hd' : IncrementsOriginalDomainConditions (normBufferedData Data b hb hbuffer))
    (hs' : IncrementsOriginalSmoothInputs (normBufferedData Data b hb hbuffer)) :
    IncrementsOriginalPhaseConditions (normBufferedData Data b hb hbuffer) hd' hs' where
  primary_good := hp.primary_good
  doubled_good := hp.doubled_good
  interaction_good := hp.interaction_good

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem normBufferedData_free_normal_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hd' : IncrementsOriginalDomainConditions (normBufferedData Data b hb hbuffer))
    (hs' : IncrementsOriginalSmoothInputs (normBufferedData Data b hb hbuffer)) :
    IncrementsOriginalFreeNormalConditions (normBufferedData Data b hb hbuffer) hd' hs' where
  unit := hn.unit
  normal := hn.normal
  free := hn.free

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem normBufferedData_immersion
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) :
    IncrementsOriginalSliceImmersionInputs (normBufferedData Data b hb hbuffer) where
  immersion := hImm.immersion

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem normBufferedData_linear_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data) :
    IncrementsOriginalLinearSmoothInputs (normBufferedData Data b hb hbuffer) where
  linear_coordinates := hLinear.linear_coordinates

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem normBufferedData_decomposition
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data) :
    IncrementsOriginalQualitativeDecompositionInputs (normBufferedData Data b hb hbuffer) where
  fiber_open := hDecomp.fiber_open
  H_symmetric := hDecomp.H_symmetric
  reference_symmetric := hDecomp.reference_symmetric
  H_mem := hDecomp.H_mem
  reference_mem := hDecomp.reference_mem
  decomposition := hDecomp.decomposition
  argument_positive := hDecomp.argument_positive

theorem normBufferedData_reserve
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho) :
    IncrementsOriginalDecompositionReserveInputs (normBufferedData Data b hb hbuffer) rho where
  reserve_pos := hReserve.reserve_pos
  lower := hReserve.lower

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem normBufferedData_ellipticity
    (Data : IncrementsOriginalNativeData n d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) :
    IncrementsOriginalCoordinateEllipticityInputs (normBufferedData Data b hb hbuffer) c where
  lower_pos := hEll.lower_pos
  lower := hEll.lower

theorem normBufferedData_transition {m : ℕ}
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (Parameter Spatial : ℕ → ℝ)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    RepairOriginalTransitionBudgets (normBufferedData Data b hb hbuffer) Parameter Spatial where
  parameter := transition.parameter
  spatial := transition.spatial

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.normBufferedData_domain_conditions
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.normBufferedData_given_profile
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.normBufferedData_phase_conditions
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.normBufferedData_transition
