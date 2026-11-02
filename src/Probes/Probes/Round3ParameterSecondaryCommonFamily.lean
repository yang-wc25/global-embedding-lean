import Probes.Round3ParameterDependentSecondaryFamily
import Probes.Round3ParameterSecondarySigmaBindings
import Probes.Round3ParameterSecondarySigmaCount

/-! Every actual signed refinement is put into one common finite index.
Inactive slots have the genuine empty chart and zero cutoff. The resulting
object supplies every field of the original JointPair consumer at all orders,
including its higher-order call, with exactly one choice. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance round3SignedRecordFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

def round3Parameter_coherent_secondary_common_family
    {Β : Type uPrimary} [Fintype Β]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Sub : ActualSecondarySignedRecord (Fin Data.primaryCount) → Type uSecondary) [∀ r, Fintype (Sub r)]
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W G : Set (Ep × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (NativeSamples : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X)
    (B : OpenPartialHomeomorph P Ep)
    (physical : (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) → Sub r →
      Round3ParameterSecondaryChoice P M m)
    (dep : Round3ParameterDependentSecondaryFamily Data Sub F hF g q ell W G
      Mrest Kcut Tinv Tobs Rsecondary NativeSamples)
    (hChoice : dep.choice = fun r a => ((physical r a).pullback B).toNative) :
    Round3ParameterPreparedSecondaryFamily (SubSecondary := Sigma Sub) Data F hF g q ell W G
      Mrest Kcut Tinv Tobs Rsecondary NativeSamples := by
  let host := fun _ : ActualSecondarySignedRecord (Fin Data.primaryCount) => Data.atlas.chart baseIndex.1
  have hHost := fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) => hd.atlas_smooth.chart_mem baseIndex.1
  let phase := fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) => actualOriginalSecondaryPhase F g r.val
  let choice := round3ParameterSecondarySigmaNativeChoice B Sub host physical
  let geometry := fun j => round3ParameterSecondarySigmaNativeGeometry F hF (actualSecondarySolveOrder q j) (j+1)
    ell (Mrest j) W B Sub host hHost phase (dep.geometry j)
  let hostIndex := fun r (a : Sigma Sub) => if h : a.1 = r then dep.hostIndex r (h ▸ a.2) else baseIndex
  have hBindings (j : ℕ) := round3Parameter_secondary_sigma_native_bindings
    F hF (actualSecondarySolveOrder q j) (j+1) ell (Mrest j) W B Sub host hHost phase
    physical (dep.geometry j)
    (fun r => incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2))
    (by simpa only [hChoice] using dep.hCoordinate j)
    (by simpa only [hChoice] using dep.hChart j) (dep.hPhase j)
    (by simpa only [hChoice] using dep.hSupport j) (dep.hPair j)
  refine {
    choice := choice
    geometry := geometry
    hCoordinate := fun j r a => (hBindings j r a).1
    hChart := fun j r a => (hBindings j r a).2.1
    hPhase := fun j r a => (hBindings j r a).2.2.1
    hHost := ?_
    hHostInv := ?_
    hHostSource := ?_
    hSupport := fun j r a => (hBindings j r a).2.2.2.1
    hPair := fun j r a => (hBindings j r a).2.2.2.2
    hPartition := ?_
    hCut := ?_
    hInv := ?_
    hCutJets := ?_
    hInvJets := ?_
    hostIndex := hostIndex
    hHostIndex := ?_
    hNativeSamples := ?_
    primaryGeometry := dep.primaryGeometry
    hOriginal := dep.hOriginal
    hChartInv := ?_
    hObserverNativeSamples := ?_
    hObserverJets := ?_
    hObserverCount := ?_ }
  · intro r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hHost r a
    · simpa only [choice,round3ParameterSecondarySigmaNativeChoice,round3ParameterSecondarySigmaChoice,h,dite_false,Round3ParameterSecondaryChoice.pullback,Round3ParameterSecondaryChoice.toNative,round3ParameterSecondaryEmptyChoice,host] using
        contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem baseIndex.1)
  · intro r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hHostInv r a
    · simpa only [choice,round3ParameterSecondarySigmaNativeChoice,round3ParameterSecondarySigmaChoice,h,dite_false,Round3ParameterSecondaryChoice.pullback,Round3ParameterSecondaryChoice.toNative,round3ParameterSecondaryEmptyChoice,host] using
        contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem baseIndex.1)
  · intro j r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hHostSource j r a
    · simp only [geometry,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,round3ParameterSecondaryEmptyNativeRawGeometry,
        round3ParameterSecondaryEmptyChoice_native_source,empty_subset]
  · intro r y hy
    change (∑ a : Sigma Sub, (round3ParameterSecondarySigmaChoice Sub host physical r a).cutoff (B.symm y.1,y.2)) = 1
    rw [round3Parameter_secondary_sigma_cutoff_sum]
    simpa only [hChoice,Round3ParameterSecondaryChoice.toNative,Round3ParameterSecondaryChoice.pullback] using dep.hPartition r y hy
  · intro j r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hCut j r a
    · simp only [choice,geometry,round3ParameterSecondarySigmaNativeChoice,round3ParameterSecondarySigmaChoice,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,Round3ParameterSecondaryChoice.toNative,
        round3ParameterSecondaryEmptyNativeRawGeometry,OpenPartialHomeomorph.trans_source,
        round3ParameterSecondaryEmptyChoice_native_source,preimage_empty,inter_empty]
      exact contDiffOn_empty
  · intro j r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hInv j r a
    · simp only [choice,geometry,round3ParameterSecondarySigmaNativeChoice,round3ParameterSecondarySigmaChoice,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,Round3ParameterSecondaryChoice.toNative,
        round3ParameterSecondaryEmptyNativeRawGeometry,OpenPartialHomeomorph.trans_target,
        round3ParameterSecondaryEmptyChoice_native_target,empty_inter]
      exact contDiffOn_empty
  · intro j r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hCutJets j r a
    · dsimp only
      intro k hk z hz
      simp only [geometry,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,round3ParameterSecondaryEmptyNativeRawGeometry,
        mem_empty_iff_false] at hz
  · intro j r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hInvJets j r a
    · dsimp only
      intro k hk hkj z hz
      simp only [geometry,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,round3ParameterSecondaryEmptyNativeRawGeometry,
        mem_empty_iff_false] at hz
  · intro r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,round3ParameterSecondarySigmaNativeChoice_active,hostIndex,dite_true,hChoice] using dep.hHostIndex r a
    · simp only [choice,round3ParameterSecondarySigmaNativeChoice,round3ParameterSecondarySigmaChoice,h,dite_false,Round3ParameterSecondaryChoice.pullback,Round3ParameterSecondaryChoice.toNative,round3ParameterSecondaryEmptyChoice,hostIndex,host]
  · intro j r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,
        hostIndex,dite_true,hChoice] using dep.hNativeSamples j r a
    · simp only [geometry,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,round3ParameterSecondaryEmptyNativeRawGeometry,
        image_empty,empty_subset]
  · intro j r ⟨s,a⟩
    by_cases h : s = r
    · subst s
      simpa only [choice,geometry,round3ParameterSecondarySigmaNativeChoice_active,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] using dep.hChartInv j r a
    · simp only [geometry,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,round3ParameterSecondaryEmptyNativeRawGeometry,
        round3ParameterSecondaryEmptyChoice_native_target]
      exact contMDiffOn_empty
  · intro j i r ⟨s,a⟩ z hz
    by_cases h : s = r
    · subst s
      simp only [geometry,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] at hz ⊢
      exact dep.hObserverNativeSamples j i r a z hz
    · simp only [geometry,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,round3ParameterSecondaryEmptyNativeRawGeometry,
        preimage_empty,inter_empty,mem_empty_iff_false] at hz
  · intro j i r ⟨s,a⟩ z hz
    by_cases h : s = r
    · subst s
      simp only [geometry,round3ParameterSecondarySigmaNativeGeometry_active,hChoice] at hz ⊢
      exact dep.hObserverJets j i r a z hz
    · simp only [geometry,round3ParameterSecondarySigmaNativeGeometry,h,dite_false,round3ParameterSecondaryEmptyNativeRawGeometry,
        preimage_empty,inter_empty,mem_empty_iff_false] at hz
  · intro j i r z hz
    change (Finset.univ.filter (fun a : Sigma Sub => (z.1,(Data.atlas.chart i.1).symm z.2) ∈
      (round3ParameterSecondarySigmaNativeGeometry F hF (actualSecondarySolveOrder q j) (j+1)
        ell (Mrest j) W B Sub host hHost phase (dep.geometry j) r a).support)).card ≤ Rsecondary
    rw [round3Parameter_secondary_sigma_support_card]
    exact dep.hObserverCount j i r z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3Parameter_coherent_secondary_common_family
