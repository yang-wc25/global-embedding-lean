import Probes.ActualIncrementSecondaryCanonicalRawData
import Probes.ActualIncrementRawJointRegularity

/-! The prepared constructor derives full-valid-set joint smoothness from its same final observer profiles. No primary smoothness record is an extra input. Actual source coverage handles an empty source correctly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N pcount : ℕ} {Ep M Tr Label SubPrimary SubSecondary : Type*}
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

theorem actual_prepared_original_increment_joint_contMDiffOn
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
    (A : BufferedAtlas M D) (ip : Fin pcount) (Samples : Fin A.count × Fin pcount → Set X)
    (finalRaw : ∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar G primary (A.chart i.1) (actualRawObserverOpen (A.chart i.1) G) (Samples i) tau ell Delta)
    (hostIndex : ActualSecondarySignedRecord Label → SubSecondary → (Fin A.count × Fin pcount))
    (hHostIndex : ∀ r a, (choice r a).host = A.chart (hostIndex r a).1)
    (hSamples : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans (geom r a).chart).symm '' (geom r a).sample ⊆ Samples (hostIndex r a))
    (primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g)
    (hq : 1 ≤ q) (hInput : nSolve+2+(q+2) ≤ nInput) (hc : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (actualOriginalIncrementMap F hF g input (q+2) tau delta
        (fun r a => (choice r a).restrictOpen G hG)) G := by
  let raw := actual_secondary_raw_data_from_canonical_prepared
    nInput nSolve j q Rsub Lprimary reserve Bnd Mg Kcut T Tinv F hF g input inputbar
    W G hW hG hGW primary ell delta tau Delta choice geom hCoordinate hChart hPhase
    hHost hHostInv hHostSource hSupport hPair hPartition hCut hInv hCutJets hInvJets
    (fun i : Fin A.count × Fin pcount => A.chart i.1) Samples finalRaw hostIndex hHostIndex hSamples primaryGeometry
  intro z hz
  obtain ⟨a,_ha⟩ := A.cover z.2
  have hraw := finalRaw (a,ip)
  exact (actual_original_increment_raw_joint_contMDiffOn nInput nSolve j q Rsub Lprimary hq hInput
    reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv hT hTinv F hF g input inputbar G primary ell delta tau Delta
    hraw.htau hraw.prim (fun r a => (choice r a).restrictOpen G hG) raw) z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_prepared_original_increment_joint_contMDiffOn
