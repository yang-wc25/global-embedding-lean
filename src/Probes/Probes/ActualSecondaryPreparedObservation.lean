import Probes.ActualSecondaryRawMetricData
import Probes.ActualIncrementRawObserverDomains
import Probes.ActualRawProfileRestriction

/-! The actual canonical observer data are constructed from the SAME raw
secondary family and genuine geometric transitions. Active domains and all
qualitative transition statements are produced internally. No wave, forcing,
metric-error or observation-output budget is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr Label SubPrimary SubSecondary : Type*}
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

def actual_secondary_observation_from_geometry
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hj : j ≤ nSolve)
    (reserve Bnd Mg Kcut : ℝ) (T Tinv Tobs : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (ell delta tau Delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
      reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice)
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ e.symm e.target)
    (S : Set X)
    (finalRaw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e (actualRawObserverOpen e W) S tau ell Delta)
    (hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (fun y : Ep × M => F y.1 y.2) W)
    (hInv : ∀ r a, ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (raw.geometry r a).chart.symm (raw.geometry r a).chart.target)
    (hSamples : ∀ r a z, z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' (raw.geometry r a).support →
      (raw.geometry r a).chart (z.1,e.symm z.2) ∈ (raw.geometry r a).sample)
    (hJets : ∀ r a z, z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' (raw.geometry r a).support →
      ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
        ((raw.geometry r a).chart ∘ (fun z : X => (z.1,e.symm z.2))) z‖ ≤ Tobs k)
    (hCount : ∀ r : ActualSecondarySignedRecord Label, ∀ z ∈ S,
      (Finset.univ.filter (fun a => (z.1,e.symm z.2) ∈ (raw.geometry r a).support)).card ≤ Rsecondary) :
    ActualOriginalSecondaryObservationData raw Tobs Rsecondary e (actualRawObserverOpen e W) S := by
  let kappa := fun z : X => (z.1,e.symm z.2)
  let O := actualRawObserverOpen e W
  let domains := fun r a => O ∩ kappa ⁻¹' (raw.geometry r a).chart.source
  have hk : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ kappa (univ ×ˢ e.target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (heInv.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have hkO := hk.mono (show O ⊆ univ ×ˢ e.target from inter_subset_left)
  have hb : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞
      (fun y : Ep × M => (y.1,e y.2)) (univ ×ˢ e.source) :=
    contMDiff_fst.contMDiffOn.prodMk_space
      (he.comp contMDiff_snd.contMDiffOn (fun (y : Ep × M) (hy : y ∈ univ ×ˢ e.source) => hy.2))

  refine {
    forward := he
    inverse := heInv
    profiles := actual_raw_profiles_restrict_observer nInput (q+2) nSolve j Rsub Lprimary hj
      reserve Bnd Mg T F hF g input inputbar W primary e O S O S tau ell Delta finalRaw
      finalRaw.hO (subset_refl _) (subset_refl _) finalRaw.hSO
    target := fun z hz => hz.1.2
    originalSmooth := (hOriginal.comp hkO (fun _ hz => hz.2)).contDiffOn
    transition := ?_
    inverseTransition := ?_
    domains := domains
    openDomains := fun r a => finalRaw.hkappaO.isOpen_inter_preimage finalRaw.hO (raw.geometry r a).chart.open_source
    domainsSubset := fun _ _ => inter_subset_left
    activeDomains := fun r a z hz => ⟨finalRaw.hSO hz.1,(raw.geometry r a).support_source hz.2⟩
    source := fun _ _ _ hz => hz.2
    samples := hSamples
    transitionJets := hJets
    localCount := hCount }
  · intro r a
    exact ((raw.geometry r a).chart_smooth.comp
      (hk.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)).contDiffOn
  · intro r a
    exact (hb.comp ((hInv r a).mono (fun _ hz => hz.1)) (fun _ hz => hz.2)).contDiffOn

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_observation_from_geometry
