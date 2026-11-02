import NormalPolar.PassiveOriginalSignedObserverFields
import NormalPolar.PassiveRawObserverTransfer

/-! The physical sample used by an additional host is constructed from the
unchanged original coordinate norm sample. Its image is exactly that original
sample. Thus the rehosted raw profiles do not require a larger norm or a new
choice of the original observer atlas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

def passiveOriginalSpatialNormSample
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (i : Fin Data.atlas.count) : Set M :=
  (Data.atlas.chart i).symm '' Data.sourceNormDomain i

theorem passiveOriginal_spatial_norm_sample
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count) (hOmega : IsCompact (Data.sourceNormDomain i)) :
    IsCompact (passiveOriginalSpatialNormSample Data i) ∧
      passiveOriginalSpatialNormSample Data i ⊆ (Data.atlas.chart i).source ∧
      (Data.atlas.chart i) '' passiveOriginalSpatialNormSample Data i = Data.sourceNormDomain i := by
  let e := Data.atlas.chart i
  refine ⟨hOmega.image_of_continuousOn (e.symm.continuousOn.mono (hd.source_norm_subset i)),?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact e.map_target (hd.source_norm_subset i hy)
  · ext y
    constructor
    · rintro ⟨x,⟨z,hz,rfl⟩,rfl⟩
      change e (e.symm z) ∈ Data.sourceNormDomain i
      rw [e.right_inv (hd.source_norm_subset i hz)]
      exact hz
    · intro hy
      exact ⟨e.symm y,⟨y,hy,rfl⟩,e.right_inv (hd.source_norm_subset i hy)⟩

theorem passiveOriginal_native_norm_sample
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hAll : Data.parameterSet = univ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i =
      Data.parameterNormDomain i.2 ×ˢ Data.sourceNormDomain i.1 := by
  ext z
  rw [mem_preimage,actual_original_native_evaluation_iff Data hd i z]
  constructor
  · exact fun h => ⟨h.2.1,h.1⟩
  · exact fun h => ⟨h.2,h.1,by rw [hAll]; exact mem_univ _⟩

variable {phase : M → ℝ} {K O : Set M}
  {ref : JointSecondarySignedRefinement (m := m) phase K O} {ib : Fin ref.count}

theorem passiveOriginal_signed_full_norm_samples
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hAll : Data.parameterSet = univ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hQ : IsCompact (Data.parameterNormDomain i.2))
    (hOmega : IsCompact (Data.sourceNormDomain i.1))
    (b b' : JointSecondarySignedBuffer ref ib)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget) :
    let R := Data.parameterNormDomain i.2 ×ˢ
      b.adaptedActiveSample (passiveOriginalSpatialNormSample Data i.1)
    IsCompact R ∧
      R ⊆ passiveOriginalObserverDomain (Data.parameterChart i.2) (Data.atlas.chart i.1) b'.chart ∧
      MapsTo (passiveRawObserverTransition (Data.atlas.chart i.1) b'.chart) R
        ((parameterTensorModelEquiv (m+1) d) ⁻¹'
          incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet i) := by
  intro R
  have hs := passiveOriginal_spatial_norm_sample Data hd i.1 hOmega
  refine ⟨b.jointAdaptedActiveSample_compact _ _ hQ hs.1,
    b.nativeHostSample_observer_domain b' hbb (Data.parameterChart i.2) _
      (hd.parameter_norm_subset i.2) _ (Data.atlas.chart i.1) hs.2.1,?_⟩
  rw [passiveOriginal_native_norm_sample Data hd hAll i]
  have hm := b.nativeHostSample_observer_mapsTo b' (Data.parameterNormDomain i.2)
    (passiveOriginalSpatialNormSample Data i.1) (Data.atlas.chart i.1)
  rw [hs.2.2] at hm
  exact hm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_spatial_norm_sample
#print axioms GlobalEmbedding.Continuation.passiveOriginal_native_norm_sample
#print axioms GlobalEmbedding.Continuation.passiveOriginal_signed_full_norm_samples
