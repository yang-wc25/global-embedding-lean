import Probes.ActualIncrementSecondaryCanonicalRawData
import Probes.ActualSecondaryPreparedObservation

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

theorem actual_secondary_prepared_raw_observations
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hj : j ≤ nSolve)
    (reserve Bnd Mg Kcut : ℝ) (T Tinv Tobs : ℕ → ℝ)
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
    (primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g)
    (hObserver : ∀ i, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (observer i) (observer i).source)
    (hObserverInv : ∀ i, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (observer i).symm (observer i).target)
    (hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (fun y : Ep × M => F y.1 y.2) G)
    (hChartInv : ∀ r a, ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ (geom r a).chart.symm (geom r a).chart.target)
    (hObserverSamples : ∀ i r a z, z ∈ Samples i ∩ (fun z : X => (z.1,(observer i).symm z.2)) ⁻¹' (geom r a).support →
      (geom r a).chart (z.1,(observer i).symm z.2) ∈ (geom r a).sample)
    (hObserverJets : ∀ i r a z, z ∈ Samples i ∩ (fun z : X => (z.1,(observer i).symm z.2)) ⁻¹' (geom r a).support →
      ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
        ((geom r a).chart ∘ (fun z : X => (z.1,(observer i).symm z.2))) z‖ ≤ Tobs k)
    (hObserverCount : ∀ i (r : ActualSecondarySignedRecord Label), ∀ z ∈ Samples i,
      (Finset.univ.filter (fun a => (z.1,(observer i).symm z.2) ∈ (geom r a).support)).card ≤ Rsecondary) :
    let raw := actual_secondary_raw_data_from_canonical_prepared
      nInput nSolve j q Rsub Lprimary reserve Bnd Mg Kcut T Tinv F hF g input inputbar W G hW hG hGW
      primary ell delta tau Delta choice geom hCoordinate hChart hPhase hHost hHostInv hHostSource
      hSupport hPair hPartition hCut hInv hCutJets hInvJets observer Samples finalRaw hostIndex hHostIndex hSamples primaryGeometry
    Nonempty (∀ i, ActualOriginalSecondaryObservationData raw Tobs Rsecondary (observer i)
      (actualRawObserverOpen (observer i) G) (Samples i)) := by
  intro raw
  refine ⟨fun i => ?_⟩
  apply actual_secondary_observation_from_geometry nInput nSolve j q Rsub Lprimary Rsecondary hj
    reserve Bnd Mg Kcut T Tinv Tobs F hF g input inputbar G primary ell delta tau Delta
    (fun r a => (choice r a).restrictOpen G hG) raw (observer i) (hObserver i) (hObserverInv i)
    (Samples i) (finalRaw i) hOriginal
  · intro r a
    exact (hChartInv r a).mono (fun _ hz => hz.1)
  · intro r a z hz
    refine ⟨hObserverSamples i r a z ⟨hz.1,hz.2.2⟩,?_⟩
    exact (raw.geometry r a).chart.map_source ((raw.geometry r a).support_source hz.2)
  · intro r a z hz k hk hkj
    exact hObserverJets i r a z ⟨hz.1,hz.2.2⟩ k hk hkj
  · intro r z hz
    apply (Finset.card_le_card (show
      Finset.univ.filter (fun a => (z.1,(observer i).symm z.2) ∈ (raw.geometry r a).support) ⊆
      Finset.univ.filter (fun a => (z.1,(observer i).symm z.2) ∈ (geom r a).support) from ?_)).trans
      (hObserverCount i r z hz)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_prepared_raw_observations
