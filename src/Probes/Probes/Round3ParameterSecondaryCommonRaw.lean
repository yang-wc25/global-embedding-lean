import Probes.Round3ParameterSecondaryCommonFamily
import Probes.ActualFinalHostRawProfiles
import Probes.ActualSecondaryPreparedObservation

/-! The same canonical secondary family is consumed by the actual raw
finite-increment theorem. Host profiles are produced from the same final
primary input on original observers. There is no new restriction of the
choice, and no forcing, wave, output increment or metric estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
universe uM uP uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def round3Parameter_secondary_raw_from_common
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W : Set (Ep × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (Samples : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X)
    (family : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary)
      Data F hF g q ell W W Mrest Kcut Tinv Tobs Rsecondary Samples)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (nInput j Rsub Lprimary : ℕ) (reserve Bnd : ℝ) (T : ℕ → ℝ)
    (primary : Fin Data.primaryCount → Set (Ep × M)) (delta tau Delta : ℝ)
    (finalRaw : ∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := ℝ)
      nInput (q+2) (actualSecondarySolveOrder q j) Rsub Lprimary reserve Bnd (Mrest j) T
      F hF g input inputbar W primary (Data.atlas.chart i.1)
      (actualRawObserverOpen (Data.atlas.chart i.1) W) (Samples i) tau ell Delta) :
    ActualOriginalSecondaryRawData (Tr := ℝ) F hF g input inputbar
      nInput (actualSecondarySolveOrder q j) j q Rsub Lprimary
      reserve Bnd (Mrest j) (Kcut j) T Tinv W primary ell delta tau Delta family.choice where
  geometry := family.geometry j
  coordinate := family.hCoordinate j
  chart := family.hChart j
  phase := family.hPhase j
  host := family.hHost
  hostInverse := family.hHostInv
  hostSource := family.hHostSource j
  cutoffSupport := family.hSupport j
  pairSupport := family.hPair j
  partition := family.hPartition
  cutoffSmooth := family.hCut j
  inverseSmooth := family.hInv j
  hostProfiles := fun r a => Classical.choice (actual_final_host_raw_profiles
    nInput (q+2) (actualSecondarySolveOrder q j) Rsub Lprimary reserve Bnd (Mrest j) T
    F hF g input inputbar W primary (fun i => Data.atlas.chart i.1)
    (fun i => actualRawObserverOpen (Data.atlas.chart i.1) W) Samples tau ell Delta finalRaw
    (family.hostIndex r a) (family.choice r a).host (family.hHostIndex r a)
    (family.geometry j r a).chart (family.geometry j r a).sample
    (family.hHostSource j r a) (family.geometry j r a).sample_subset
    (by
      intro z hz
      rw [← family.hHostIndex r a]
      exact ⟨hz.1,(family.geometry j r a).source_domain hz.2⟩)
    (family.hNativeSamples j r a))
  cutoffJets := family.hCutJets j
  inverseJets := family.hInvJets j
  primaryGeometry := family.primaryGeometry

def round3Parameter_secondary_observation_from_common
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Β) F)
    (q : ℕ) (ell : ℝ) (W : Set (Ep × M))
    (Mrest Kcut Tinv Tobs : ℕ → ℝ) (Rsecondary : ℕ)
    (Samples : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X)
    (family : Round3ParameterPreparedSecondaryFamily (SubSecondary := SubSecondary)
      Data F hF g q ell W W Mrest Kcut Tinv Tobs Rsecondary Samples)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (nInput j Rsub Lprimary : ℕ) (reserve Bnd : ℝ) (T : ℕ → ℝ)
    (primary : Fin Data.primaryCount → Set (Ep × M)) (delta tau Delta : ℝ)
    (finalRaw : ∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := ℝ)
      nInput (q+2) (actualSecondarySolveOrder q j) Rsub Lprimary reserve Bnd (Mrest j) T
      F hF g input inputbar W primary (Data.atlas.chart i.1)
      (actualRawObserverOpen (Data.atlas.chart i.1) W) (Samples i) tau ell Delta)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ActualOriginalSecondaryObservationData
      (round3Parameter_secondary_raw_from_common Data F hF g q ell W Mrest Kcut Tinv Tobs Rsecondary Samples
        family input inputbar nInput j Rsub Lprimary reserve Bnd T primary delta tau Delta finalRaw)
      Tobs Rsecondary (Data.atlas.chart i.1) (actualRawObserverOpen (Data.atlas.chart i.1) W) (Samples i) := by
  apply actual_secondary_observation_from_geometry nInput (actualSecondarySolveOrder q j) j q Rsub Lprimary Rsecondary
    (by unfold actualSecondarySolveOrder; omega) reserve Bnd (Mrest j) (Kcut j) T Tinv Tobs F hF g input inputbar
    W primary ell delta tau Delta family.choice
    (round3Parameter_secondary_raw_from_common Data F hF g q ell W Mrest Kcut Tinv Tobs Rsecondary Samples
      family input inputbar nInput j Rsub Lprimary reserve Bnd T primary delta tau Delta finalRaw)
    (Data.atlas.chart i.1) (contMDiffOn_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1))
    (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1))
    (Samples i) (finalRaw i) family.hOriginal (family.hChartInv j)
    (family.hObserverNativeSamples j i) (family.hObserverJets j i) (family.hObserverCount j i)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_raw_from_common
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_observation_from_common
