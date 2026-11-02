import NormalPolar.PassiveOriginalObserverArgument
import NormalPolar.JointSecondarySignedNativeHost
import Probes.ActualIncrementOriginalSampling
import Smoothing.ParameterRound2OriginalFiniteReserveGerm

/-! The additional signed host uses the original parameter norm piece and
the actual image of the original spatial norm sample. Its primary-active
part is compact, lies in the true overlap, and maps into the unchanged
original primary evaluation set. No new norm domain is introduced. -/

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
local notation "IM" => 𝓘(ℝ,D)

variable {phase : M → ℝ} {K O : Set M}
  {ref : JointSecondarySignedRefinement (m := m) phase K O} {ib : Fin ref.count}

def passiveOriginalSignedObserverSample
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (b b' : JointSecondarySignedBuffer ref ib) (Q : Set Ep) (S : Set M) : Set X :=
  (Q ×ˢ b.adaptedActiveSample S) ∩
    (fun z : X => ((Data.parameterChart i.2).symm z.1,b'.chart.symm z.2)) ⁻¹'
      tsupport (Data.cutoff nu)

theorem passiveOriginal_signed_observer_samples
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hAll : Data.parameterSet = univ)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (b b' : JointSecondarySignedBuffer ref ib)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget)
    (Q : Set Ep) (hQ : IsCompact Q) (hQQ : Q ⊆ Data.parameterNormDomain i.2)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ (Data.atlas.chart i.1).source)
    (hSS : (Data.atlas.chart i.1) '' S ⊆ Data.sourceNormDomain i.1) :
    let R := passiveOriginalSignedObserverSample Data nu i b b' Q S
    IsCompact R ∧
    R ⊆ passiveOriginalObserverDomain (Data.parameterChart i.2) (Data.atlas.chart i.1) b'.chart ∧
    MapsTo (passiveOriginalObserverCoordinates (Data.atlas.chart i.1) b'.chart) R
      (incrementsOriginalPrimaryEvaluation Data nu i) := by
  intro R
  let B := Data.parameterChart i.2
  let e := Data.atlas.chart i.1
  let H := Q ×ˢ b.adaptedActiveSample S
  have hQT : Q ⊆ B.target := hQQ.trans (hd.parameter_norm_subset i.2)
  have hHC : IsCompact H := b.jointAdaptedActiveSample_compact Q S hQ hS
  have hHO : H ⊆ passiveOriginalObserverDomain B e b'.chart :=
    b.nativeHostSample_observer_domain b' hbb B Q hQT S e hSe
  have hHT : H ⊆ (B.prod b'.chart).target := fun z hz =>
    ⟨(hHO hz).1,(hHO hz).2.1⟩
  have hRC : IsCompact R := hHC.of_isClosed_subset
    (((B.prod b'.chart).symm.continuousOn.mono hHT).preimage_isClosed_of_isClosed
      hHC.isClosed (isClosed_tsupport (Data.cutoff nu))) inter_subset_left
  refine ⟨hRC,fun z hz => hHO hz.1,?_⟩
  intro z hz
  have hzO := hHO hz.1
  have hMaps := b.nativeHostSample_observer_mapsTo b' Q S e hz.1
  have hEval : passiveOriginalObserverCoordinates e b'.chart z ∈
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i := by
    apply (actual_original_native_evaluation_iff Data hd i
      (z.1,e (b'.chart.symm z.2))).mpr
    exact ⟨hSS hMaps.2,hQQ hMaps.1,by rw [hAll]; exact mem_univ _⟩
  refine ⟨hEval,?_⟩
  change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
    (passiveOriginalObserverCoordinates (Data.atlas.chart i.1) b'.chart z) ∈ Data.primaryDomain nu
  rw [passiveOriginalObserverCoordinates_point Data.atlas Data.parameterChart i b'.chart z hzO]
  apply hd.cutoff_support_local nu
  rw [parameterRound2_original_relativeSupport_eq Data hd.parameter_open]
  exact ⟨⟨hd.parameter_subset (by rw [hAll]; exact mem_univ _),mem_univ _⟩,hz.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_signed_observer_samples
