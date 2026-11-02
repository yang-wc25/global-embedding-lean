import FaithfulIncrements.LocalPrimaryNeighborhoods
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs

/-!
# Original hypotheses survive internal solver-neighborhood restriction

Source: main.tex, lem:increments, especially the subordinate adapted-chart step
and the support-preserving finite construction.  The input datum is retained;
`localPrimaryData` changes only internal open-domain annotations.  All field
functions, coordinate norm domains, compact parameter samples and decomposition
neighborhoods are literally unchanged.  No quantitative conclusion is assumed.

These lemmas transfer every original qualitative input to the one manufactured
local datum, so the local construction does not request new phase or normal
conditions from its caller.  They do not replace the original output norms.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulIntegration
open FaithfulIncrements

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem localPrimaryData_phase_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (hd' : IncrementsOriginalDomainConditions (localPrimaryData Data V domain))
    (hs' : IncrementsOriginalSmoothInputs (localPrimaryData Data V domain)) :
    IncrementsOriginalPhaseConditions (localPrimaryData Data V domain) hd' hs' where
  primary_good := fun nu z hz => hp.primary_good nu z
    ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩
  doubled_good := fun nu z hz => hp.doubled_good nu z
    ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩
  interaction_good := fun nu mu hne sign z hz => hp.interaction_good nu mu hne sign z
    ⟨localPrimaryData_relative_support_subset Data V domain hV nu hz.1,
      localPrimaryData_relative_support_subset Data V domain hV mu hz.2⟩

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem localPrimaryData_free_normal_conditions
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (hd' : IncrementsOriginalDomainConditions (localPrimaryData Data V domain))
    (hs' : IncrementsOriginalSmoothInputs (localPrimaryData Data V domain)) :
    IncrementsOriginalFreeNormalConditions (localPrimaryData Data V domain) hd' hs' where
  unit := fun nu z hz => hn.unit nu z ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩
  normal := fun nu z hz => hn.normal nu z ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩
  free := fun nu z hz u v => hn.free nu z ⟨hDomain nu hz.1, hV hz.2.1, hz.2.2⟩ u v

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem localPrimaryData_slice_immersion
    (Data : IncrementsOriginalNativeData n d N M P)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) :
    IncrementsOriginalSliceImmersionInputs (localPrimaryData Data V domain) where
  immersion := fun p hp x => hImm.immersion p (hV hp) x

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem localPrimaryData_linear_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu) :
    IncrementsOriginalLinearSmoothInputs (localPrimaryData Data V domain) where
  linear_coordinates := fun nu i => (hLinear.linear_coordinates nu i).mono
    (fun _ hy => ⟨⟨hy.1.1, hDomain nu hy.1.2⟩, hV hy.2.1, hy.2.2⟩)

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem localPrimaryData_decomposition
    (Data : IncrementsOriginalNativeData n d N M P)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) :
    IncrementsOriginalQualitativeDecompositionInputs (localPrimaryData Data V domain) where
  fiber_open := fun p hp x => hDecomp.fiber_open p (hV hp) x
  H_symmetric := fun p hp x => hDecomp.H_symmetric p (hV hp) x
  reference_symmetric := fun p hp x => hDecomp.reference_symmetric p (hV hp) x
  H_mem := fun p hp x => hDecomp.H_mem p (hV hp) x
  reference_mem := fun p hp x => hDecomp.reference_mem p (hV hp) x
  decomposition := fun p hp x A hA => hDecomp.decomposition p (hV hp) x A hA
  argument_positive := fun p hp x nu hcut A hA =>
    hDecomp.argument_positive p (hV hp) x nu hcut A hA

theorem localPrimaryData_reserve
    (Data : IncrementsOriginalNativeData n d N M P)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) :
    IncrementsOriginalDecompositionReserveInputs (localPrimaryData Data V domain) rho where
  reserve_pos := hReserve.reserve_pos
  lower := fun nu z hz hK A hA => hReserve.lower nu z
    (localPrimaryData_relative_support_subset Data V domain hV nu hz) hK A hA

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
theorem localPrimaryData_ellipticity
    (Data : IncrementsOriginalNativeData n d N M P)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)) :
    IncrementsOriginalCoordinateEllipticityInputs (localPrimaryData Data V domain) c where
  lower_pos := hEll.lower_pos
  lower := hEll.lower

omit [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] in
/-- The final open neighborhood remains inside the original parameter region;
the same U and every original sample and coordinate expression are preserved. -/
theorem localPrimaryData_output_region
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (G : Set (P × M))
    (hG : G ⊆ incrementsOriginalParameterRegion (localPrimaryData Data V domain)) :
    G ⊆ incrementsOriginalParameterRegion Data :=
  fun _ hz => ⟨hV (hG hz).1, (hG hz).2⟩

end GlobalEmbedding.Continuation.FaithfulIntegration

#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.localPrimaryData_phase_conditions
#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.localPrimaryData_free_normal_conditions
#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.localPrimaryData_decomposition
#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.localPrimaryData_reserve
