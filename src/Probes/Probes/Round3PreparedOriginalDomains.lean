import Probes.Round3PhaseSignedPreparation

/-! Exact original domain transport for the actual secondary preparation. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round3_prepared_native_primary_mem
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (z : X) (hzs : z.2 ∈ (Data.atlas.chart i.1).target)
    (hzp : z.1 ∈ (Data.parameterChart i.2).target)
    (hactive : ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    z ∈ actualOriginalPrimaryNativeOpen Data nu i := by
  have he := (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
  have hp := congrArg Prod.fst he
  have hx := congrArg Prod.snd he
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z) = z.1 at hp
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at hx
  change ((parameterTensorModelEquiv (m+1) d z ∈
    incrementsOriginalDifferentiation Data.atlas Data.parameterChart i) ∧
    incrementsOriginalJointPoint Data.atlas Data.parameterChart i (parameterTensorModelEquiv (m+1) d z) ∈
      Data.primaryDomain nu) ∧
    incrementsOriginalJointPoint Data.atlas Data.parameterChart i (parameterTensorModelEquiv (m+1) d z) ∈
      incrementsOriginalParameterRegion Data
  rw [actual_original_jointPoint_native]
  refine ⟨⟨?_,hactive.1⟩,hactive.2⟩
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) ∈ (Data.atlas.chart i.1).target ∧
    incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z) ∈ (Data.parameterChart i.2).target
  simpa only [hx,hp] using And.intro hzs hzp

theorem round3_prepared_native_primary_active
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    {z : X} (hz : z ∈ actualOriginalPrimaryNativeOpen Data nu i) :
    ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
  have h1 := hz.1.2
  have h2 := hz.2
  simp only [Set.mem_preimage] at h1 h2
  rw [actual_original_jointPoint_native] at h1 h2
  exact ⟨h1,h2⟩

theorem round3_prepared_primary_native_subset
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount) :
    actualOriginalPrimaryNativeOpen Data nu i ⊆ actualOriginalNativeOpen Data i :=
  fun _ hz => ⟨hz.1.1,hz.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_prepared_native_primary_mem
#print axioms GlobalEmbedding.Continuation.round3_prepared_native_primary_active
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_native_subset
