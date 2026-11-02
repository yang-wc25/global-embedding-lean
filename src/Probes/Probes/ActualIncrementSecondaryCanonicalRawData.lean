import Probes.ActualSecondaryRawMetricData
import Probes.ActualIncrementSecondaryGeometryRestriction
import Probes.ActualIncrementSecondaryChoiceRestriction
import Probes.ActualFinalHostRawProfiles
import Probes.ActualFinalCanonicalHostDomains
import Probes.ActualIncrementSecondaryPreparedRawData

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

def actual_secondary_raw_data_from_canonical_prepared
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
    (observer : Index → OpenPartialHomeomorph M D) (Samples : Index → Set X)
    (finalRaw : ∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar G primary (observer i) (actualRawObserverOpen (observer i) G) (Samples i) tau ell Delta)
    (hostIndex : ActualSecondarySignedRecord Label → SubSecondary → Index)
    (hHostIndex : ∀ r a, (choice r a).host = observer (hostIndex r a))
    (hSamples : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans (geom r a).chart).symm '' (geom r a).sample ⊆ Samples (hostIndex r a))
    (primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g) :
    ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
      reserve Bnd Mg Kcut T Tinv G primary ell delta tau Delta
      (fun r a => (choice r a).restrictOpen G hG) := by
  apply actual_secondary_raw_data_from_prepared nInput nSolve j q Rsub Lprimary reserve Bnd Mg Kcut T Tinv
    F hF g input inputbar W G hW hG hGW primary ell delta tau Delta choice geom
    hCoordinate hChart hPhase hHost hHostInv hHostSource hSupport hPair hPartition hCut hInv hCutJets hInvJets
    observer (fun i => actualRawObserverOpen (observer i) G) Samples finalRaw hostIndex hHostIndex ?_ ?_ primaryGeometry
  · intro r a
    simpa only [hHostIndex r a] using
      actual_secondary_host_source_subset_canonical_observer (choice r a).host
        ((geom r a).restrictOpen G hG hGW).chart G ((geom r a).restrictOpen G hG hGW).source_domain
  · intro r a
    dsimp only
    rintro z ⟨w,hw,rfl⟩
    exact hSamples r a ⟨w,hw.1,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_raw_data_from_canonical_prepared
