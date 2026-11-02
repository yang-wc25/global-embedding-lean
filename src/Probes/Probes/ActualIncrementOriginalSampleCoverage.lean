import Smoothing.ParameterRound2OriginalArgumentContinuity

/-! The literal original evaluation sets cover every source point above the
entire original parameter set. Therefore their actual image-containment
conclusion implies K times M containment, without strengthening a final supply. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem actual_original_sample_images_cover_parameter_source
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (G : Set (P × M))
    (hSamples : ∀ i, MapsTo (incrementsOriginalJointPoint D.atlas D.parameterChart i)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet i) G) :
    D.parameterSet ×ˢ (univ : Set M) ⊆ G := by
  intro z hz
  obtain ⟨a,ha⟩ := D.atlas.cover z.2
  obtain ⟨b,hb,hbn⟩ := hd.parameter_cover z.1 hz.1
  let i : Fin D.atlas.count × Fin D.parameterCount := (a,b)
  let y := parameterRound2_originalForwardCoordinates D i z
  have hx : z.2 ∈ (D.atlas.chart i.1).source := D.atlas.inner_subset a ha
  have hp : z.1 ∈ (D.parameterChart i.2).source := hb
  have he : incrementsOriginalJointPoint D.atlas D.parameterChart i y = z :=
    parameterRound2_originalForward_left_inv D i z hp hx
  have hm := parameterRound2_originalForward_mem D i z hp hx
  have hc := parameterRound2_originalForward_components D i z
  have hp' : incrementsOriginalParameterPoint y = D.parameterChart i.2 z.1 := congrArg Prod.fst hc
  have hx' : incrementsOriginalSourcePoint y = D.atlas.chart i.1 z.2 := congrArg Prod.snd hc
  have hy : y ∈ incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet i := by
    refine ⟨hm,?_,?_,?_⟩
    · rw [hx']
      exact hd.source_inner_norm a z.2 ha
    · rw [hp']
      exact hbn
    · change (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1 ∈ D.parameterSet
      rw [he]
      exact hz.1
  simpa only [he] using hSamples i hy

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_sample_images_cover_parameter_source
