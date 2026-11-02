import Probes.ActualSecondaryRawMetricData
import Probes.ActualIncrementSecondaryGeometryRestriction
import Probes.ActualIncrementSecondaryChoiceRestriction
import Probes.ActualFinalHostRawProfiles

/-! Prepared original secondary geometry supplies the SAME final-germ raw
family. Only actual chart domains and the genuine cutoff/pair supports are
restricted. The final host input profiles are obtained from the actual final
iterate on original observers; no forcing, source or wave budget is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr Label SubPrimary SubSecondary Index : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def actual_secondary_raw_data_from_prepared
    (nInput nSolve j q Rsub Lprimary : ℕ) (reserve Bnd Mg Kcut : ℝ) (T Tinv : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W G : Set (Ep × M)) (hW : IsOpen W) (hG : IsOpen G) (hGW : G ⊆ W)
    (primary : Label → Set (Ep × M)) (ell delta tau Delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (geom : ActualSecondarySignedRecord Label → SubSecondary → ActualSecondaryRawGeometry F hF nSolve (j+1) ell Mg W)
    (hCoordinate : ∀ r a, (geom r a).c = (choice r a).c)
    (hChart : ∀ r a, (geom r a).chart = (choice r a).chart)
    (hPhase : ∀ r a, (geom r a).phase = actualOriginalSecondaryPhase F g r.val)
    (hHost : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (choice r a).host (choice r a).host.source)
    (hHostInv : ∀ r a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target)
    (hHostSource : ∀ r a, (geom r a).chart.source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source)
    (hSupport : ∀ r a, tsupport (fun y : W => (choice r a).cutoff y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2)) ⊆ Subtype.val ⁻¹' (geom r a).support)
    (hPair : ∀ r a, (geom r a).support ⊆ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2))
    (hPartition : ∀ r : ActualSecondarySignedRecord Label, ∀ y,
      y ∈ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2) → ∑ a, (choice r a).cutoff y = 1)
    (hCut : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ContDiffOn ℝ ∞ ((choice r a).cutoff ∘ b.symm) (b.symm.trans (geom r a).chart).source)
    (hInv : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ContDiffOn ℝ ∞ (b.symm.trans (geom r a).chart).symm (b.symm.trans (geom r a).chart).target)
    (hCutJets : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ∀ k ≤ nSolve, ∀ z ∈ (geom r a).sample, ell^k*‖iteratedFDeriv ℝ k
        ((choice r a).cutoff ∘ b.symm) ((b.symm.trans (geom r a).chart).symm z)‖ ≤ Kcut)
    (hInvJets : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ∀ k, 1 ≤ k → k ≤ nSolve+1 → ∀ z ∈ (geom r a).sample,
        ell^(k-1)*‖iteratedFDeriv ℝ k (b.symm.trans (geom r a).chart).symm z‖ ≤ Tinv k)
    (observer : Index → OpenPartialHomeomorph M D) (Obs Samples : Index → Set X)
    (finalRaw : ∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar G primary (observer i) (Obs i) (Samples i) tau ell Delta)
    (hostIndex : ActualSecondarySignedRecord Label → SubSecondary → Index)
    (hHostIndex : ∀ r a, (choice r a).host = observer (hostIndex r a))
    (hDomain : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans ((geom r a).restrictOpen G hG hGW).chart).source ⊆ Obs (hostIndex r a))
    (hSamples : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans ((geom r a).restrictOpen G hG hGW).chart).symm ''
        ((geom r a).restrictOpen G hG hGW).sample ⊆ Samples (hostIndex r a))
    (primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g) :
    ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
      reserve Bnd Mg Kcut T Tinv G primary ell delta tau Delta
      (fun r a => (choice r a).restrictOpen G hG) where
  geometry := fun r a => (geom r a).restrictOpen G hG hGW
  coordinate := hCoordinate
  chart := fun r a => by
    change (geom r a).chart.restrOpen G hG = (choice r a).chart.restrOpen G hG
    rw [hChart r a]
  phase := hPhase
  host := hHost
  hostInverse := hHostInv
  hostSource := fun r a y hy => hHostSource r a hy.1
  cutoffSupport := fun r a => actual_secondary_relative_pair_cutoff_restrict
    (choice r a).cutoff (g.cutoff r.val.1.1) (g.cutoff r.val.1.2) W G (geom r a).support hW hG hGW (hSupport r a)
  pairSupport := fun r a => actual_secondary_relative_pair_support_restrict
    (g.cutoff r.val.1.1) (g.cutoff r.val.1.2) W G (geom r a).support hW hG (hPair r a)
  partition := by
    intro r y hy
    rw [parameterRound2_global_relativeSupport_eq G hG,
      parameterRound2_global_relativeSupport_eq G hG] at hy
    apply hPartition r
    rw [parameterRound2_global_relativeSupport_eq W hW,
      parameterRound2_global_relativeSupport_eq W hW]
    exact ⟨⟨hGW hy.1.1,hy.1.2⟩,⟨hGW hy.2.1,hy.2.2⟩⟩
  cutoffSmooth := fun r a => (hCut r a).mono (fun _ hz => ⟨hz.1,hz.2.1⟩)
  inverseSmooth := fun r a => (hInv r a).mono (fun _ hz => ⟨hz.1.1,hz.2⟩)
  hostProfiles := fun r a => Classical.choice (actual_final_host_raw_profiles
    nInput (q+2) nSolve Rsub Lprimary reserve Bnd Mg T F hF g input inputbar G primary
    observer Obs Samples tau ell Delta finalRaw (hostIndex r a) (choice r a).host (hHostIndex r a)
    ((geom r a).restrictOpen G hG hGW).chart ((geom r a).restrictOpen G hG hGW).sample
    (fun _ hz => hHostSource r a hz.1) ((geom r a).restrictOpen G hG hGW).sample_subset
    (hDomain r a) (hSamples r a))
  cutoffJets := fun r a k hk z hz => hCutJets r a k hk z hz.1
  inverseJets := fun r a k hk hk' z hz => hInvJets r a k hk hk' z hz.1
  primaryGeometry := primaryGeometry

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_raw_data_from_prepared
