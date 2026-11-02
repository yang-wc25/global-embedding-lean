import FaithfulCollars.RefinedWorkingAtlas
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs
import Probes.ActualOriginalGivenProfile
import Repair.EntranceOriginalObserverJets

/-!
# Exact original-data transport for manufactured general collar refinements

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

def refinedWorkingData (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb) :
    IncrementsOriginalNativeData n d N M P :=
  { Data with atlas := originalRefinedWorkingAtlas Data.atlas Data.sourceNormDomain R b hb hbuffer s }

theorem refinedWorkingData_given_profile
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb) (j : ℕ) (ell : ℝ) :
    actualOriginalGivenInputProfile (refinedWorkingData Data R b hb hbuffer s) j ell =
      actualOriginalGivenInputProfile Data j ell := rfl

theorem refinedWorkingData_source_sampling
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i) :
    ∀ i, bufferedSamplingCoordinates (refinedWorkingData Data R b hb hbuffer s).atlas i ⊆
      (refinedWorkingData Data R b hb hbuffer s).sourceNormDomain i :=
  fun i => (refinedWorkingAtlas_sampling_subset_original Data.atlas Data.sourceNormDomain R b hb hbuffer s i).trans (hSource i)

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem refinedWorkingData_domain_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hd : IncrementsOriginalDomainConditions Data)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i) :
    IncrementsOriginalDomainConditions (refinedWorkingData Data R b hb hbuffer s) where
  source_dim := hd.source_dim
  target_dim := hd.target_dim
  parameter_open := hd.parameter_open
  parameter_compact := hd.parameter_compact
  parameter_subset := hd.parameter_subset
  atlas_smooth := refinedWorkingAtlas_smooth Data.atlas Data.sourceNormDomain R b hb hbuffer s hd.atlas_smooth
  parameter_charts_smooth := hd.parameter_charts_smooth
  source_norm_subset := hd.source_norm_subset
  source_inner_norm := fun i x hx => hSource i (refinedWorkingAtlas_inner_sampling Data.atlas Data.sourceNormDomain R b hb hbuffer s i x hx)
  parameter_norm_subset := hd.parameter_norm_subset
  parameter_cover := hd.parameter_cover
  primary_open := hd.primary_open
  cutoff_support_local := hd.cutoff_support_local

theorem refinedWorkingData_smooth_inputs
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hs : IncrementsOriginalSmoothInputs Data) :
    IncrementsOriginalSmoothInputs (refinedWorkingData Data R b hb hbuffer s) where
  F_joint := hs.F_joint
  H_coordinates := hs.H_coordinates
  phase_joint := hs.phase_joint
  cutoff_joint := hs.cutoff_joint
  normal_joint := hs.normal_joint

theorem refinedWorkingData_phase_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hd' : IncrementsOriginalDomainConditions (refinedWorkingData Data R b hb hbuffer s))
    (hs' : IncrementsOriginalSmoothInputs (refinedWorkingData Data R b hb hbuffer s)) :
    IncrementsOriginalPhaseConditions (refinedWorkingData Data R b hb hbuffer s) hd' hs' where
  primary_good := hp.primary_good
  doubled_good := hp.doubled_good
  interaction_good := hp.interaction_good

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem refinedWorkingData_free_normal_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hd' : IncrementsOriginalDomainConditions (refinedWorkingData Data R b hb hbuffer s))
    (hs' : IncrementsOriginalSmoothInputs (refinedWorkingData Data R b hb hbuffer s)) :
    IncrementsOriginalFreeNormalConditions (refinedWorkingData Data R b hb hbuffer s) hd' hs' where
  unit := hn.unit
  normal := hn.normal
  free := hn.free

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem refinedWorkingData_immersion
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) :
    IncrementsOriginalSliceImmersionInputs (refinedWorkingData Data R b hb hbuffer s) where
  immersion := hImm.immersion

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem refinedWorkingData_linear_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data) :
    IncrementsOriginalLinearSmoothInputs (refinedWorkingData Data R b hb hbuffer s) where
  linear_coordinates := hLinear.linear_coordinates

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem refinedWorkingData_decomposition
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data) :
    IncrementsOriginalQualitativeDecompositionInputs (refinedWorkingData Data R b hb hbuffer s) where
  fiber_open := hDecomp.fiber_open
  H_symmetric := hDecomp.H_symmetric
  reference_symmetric := hDecomp.reference_symmetric
  H_mem := hDecomp.H_mem
  reference_mem := hDecomp.reference_mem
  decomposition := hDecomp.decomposition
  argument_positive := hDecomp.argument_positive

theorem refinedWorkingData_reserve
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho) :
    IncrementsOriginalDecompositionReserveInputs (refinedWorkingData Data R b hb hbuffer s) rho where
  reserve_pos := hReserve.reserve_pos
  lower := hReserve.lower

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem refinedWorkingData_ellipticity
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) :
    IncrementsOriginalCoordinateEllipticityInputs (refinedWorkingData Data R b hb hbuffer s) c where
  lower_pos := hEll.lower_pos
  lower := hEll.lower

theorem refinedWorkingData_transition {m : ℕ}
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (Parameter Spatial : ℕ → ℝ)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    RepairOriginalTransitionBudgets (refinedWorkingData Data R b hb hbuffer s) Parameter Spatial where
  parameter := transition.parameter
  spatial := transition.spatial

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.refinedWorkingData_domain_conditions
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.refinedWorkingData_given_profile
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.refinedWorkingData_phase_conditions
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.refinedWorkingData_transition
