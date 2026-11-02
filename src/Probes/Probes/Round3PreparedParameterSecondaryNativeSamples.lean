import Probes.Round3PreparedParameterSecondaryNativeCarrier
import Probes.Round3PreparedHostSamples
import Probes.ActualIncrementOriginalSampling

/-! One actual secondary sample is used by every later order. It consists
of the effective carrier points whose original host coordinates belong to
the original norm domain. All original observers map into this same sample. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

 def round3PreparedParameterSecondarySample
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (a : OpenPartialHomeomorph (Ep × M) X) (carrier : Set (Ep × M)) : Set X :=
    a '' {y | y ∈ carrier ∧ parameterTensorModelEquiv (m+1) d
      (y.1,Data.atlas.chart i.1 y.2) ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i}

 theorem round3_prepared_parameter_secondary_native_samples
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D) (phase : Ep × M → ℝ)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b phase e)
    (carrier : Set (Ep × M))
    (hCarrier : carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hInner : ∀ y ∈ carrier, y.2 ∈ Data.atlas.inner i.1) :
    let a := actualHostAdaptedChart (Data.atlas.chart i.1) b
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
    let S := round3PreparedParameterSecondarySample Data i a carrier
    S ⊆ b.target ∧
    MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i) ∧
    (q.symm.trans a).symm '' S ⊆ (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i ∧
    ∀ observer z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas
      Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet (observer,i.2) →
      (z.1,(Data.atlas.chart observer).symm z.2) ∈ carrier →
      a (z.1,(Data.atlas.chart observer).symm z.2) ∈ S := by
  intro a q S
  have hNative := (actual_host_slice_geometry_inputs (Data.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1) b phase e hdata).1
  have hSb : S ⊆ b.target := by
    rintro _ ⟨y,hy,rfl⟩
    rw [← hdata.1]
    exact a.map_source (hCarrier hy.1)
  have hBack (y : Ep × M) (hy : y ∈ carrier) : b.symm (a y) = q y :=
    b.left_inv (hCarrier hy).2
  have hSample : MapsTo b.symm S ((parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i) := by
    rintro _ ⟨y,hy,rfl⟩
    rw [hBack y hy.1]
    exact hy.2
  refine ⟨hSb,hSample,?_,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    rw [(round3_prepared_host_transition_domains (Data.atlas.chart i.1) b hNative).2.2.2 (hSb hz)]
    exact hSample hz
  · intro observer z hz hCarrierZ
    refine ⟨(z.1,(Data.atlas.chart observer).symm z.2),⟨hCarrierZ,?_⟩,rfl⟩
    have hObs := (actual_original_native_evaluation_iff Data hd (observer,i.2) z).mp hz
    exact (actual_original_native_evaluation_iff Data hd i _).mpr
      ⟨hd.source_inner_norm i.1 _ (hInner _ hCarrierZ),hObs.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_native_samples
