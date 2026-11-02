import Probes.Round3PreparedOriginalDomains
import Probes.ActualIncrementOriginalSampling

/-! The true original observer samples form one compact physical set.
Their transport into a parent host follows from the actual inner support and
the frozen source-norm inclusion; it is not a separate sample certificate. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

def round3PreparedOriginalNativeSamples (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) : Set X :=
  (parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i

theorem round3_prepared_original_native_samples_compact
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)) :
    ∀ i, IsCompact (round3PreparedOriginalNativeSamples Data i) := by
  intro i
  let e := parameterTensorModelEquiv (m+1) d
  have he : round3PreparedOriginalNativeSamples Data i = e.symm ''
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i := by
    ext z
    constructor
    · intro hz
      exact ⟨e z,hz,e.symm_apply_apply z⟩
    · rintro ⟨w,hw,rfl⟩
      change e (e.symm w) ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i
      rwa [e.apply_symm_apply]
  rw [he]
  exact (hS i).image e.symm.continuous

theorem round3_prepared_original_samples
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (hId : Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)) :
    ∃ K : Set (Ep × M), IsCompact K ∧
      K ⊆ Data.parameterSet ×ˢ (univ : Set M) ∧
      (∀ i, round3PreparedOriginalNativeSamples Data i ⊆
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).target) ∧
      (∀ i, MapsTo (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2))
        (round3PreparedOriginalNativeSamples Data i) K) ∧
      ∀ host : Fin Data.atlas.count, MapsTo
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart host))
        (K ∩ (fun y : Ep × M => y.2) ⁻¹' Data.atlas.inner host)
        (round3PreparedOriginalNativeSamples Data (host,ip)) := by
  have heq (jp : Fin Data.parameterCount) : jp = ip := by
    letI : Subsingleton (Fin Data.parameterCount) := by rw [hOne]; infer_instance
    exact Subsingleton.elim _ _
  have hIdAll (jp : Fin Data.parameterCount) : Data.parameterChart jp = OpenPartialHomeomorph.refl Ep := by
    rw [heq jp]
    exact hId
  let kappa := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2)
  let K := ⋃ i, kappa i '' round3PreparedOriginalNativeSamples Data i
  have hNative := round3_prepared_original_native_samples_compact Data hS
  have hTarget (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      round3PreparedOriginalNativeSamples Data i ⊆
        (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).target := by
    intro z hz
    exact ⟨Set.mem_univ _,actualOriginalNativeMap_source_target Data i hz.1⟩
  have hK : IsCompact K := isCompact_iUnion (fun i =>
    (hNative i).image_of_continuousOn
      ((actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm.continuousOn.mono (hTarget i)))
  have hKparam : K ⊆ Data.parameterSet ×ˢ (univ : Set M) := by
    intro y hy
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hy
    have hp := (actualOriginalNativeMap_evaluation_members Data i hz).2
    simpa only [kappa,hIdAll,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,
      mem_prod,mem_univ,and_true] using hp
  refine ⟨K,hK,hKparam,hTarget,?_,?_⟩
  · intro i z hz
    exact mem_iUnion.mpr ⟨i,z,hz,rfl⟩
  · intro host y hy
    have hp := (hKparam hy.1).1
    obtain ⟨jp,hjp,hQ⟩ := hd.parameter_cover y.1 hp
    have hQ' : y.1 ∈ Data.parameterNormDomain ip := by
      simpa only [heq jp,hId,OpenPartialHomeomorph.refl_apply,id_eq] using hQ
    apply (actual_original_native_evaluation_iff Data hd (host,ip) _).2
    change Data.atlas.chart host y.2 ∈ Data.sourceNormDomain host ∧
      y.1 ∈ Data.parameterNormDomain ip ∧ (Data.parameterChart ip).symm y.1 ∈ Data.parameterSet
    exact ⟨hd.source_inner_norm host y.2 hy.2,hQ',by simpa only [hId,OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply,id_eq] using hp⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_prepared_original_native_samples_compact
#print axioms GlobalEmbedding.Continuation.round3_prepared_original_samples
