import Smoothing.ParameterRound2MeanRawProfiles

/-! Actual observer and piece domains for the original raw mean consumer.
They are built from the SAME chart maps and relative cutoff supports. No
extra transition identity or output regularity is inserted as a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualRawObserverOpen (e : OpenPartialHomeomorph M D) (W : Set (Ep × M)) : Set X :=
  (univ ×ˢ e.target) ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' W

theorem actual_raw_observer_domains
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (prim : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
    (S : Set X) (hSO : S ⊆ actualRawObserverOpen e W) :
    let kappa := fun z : X => (z.1,e.symm z.2)
    let O := actualRawObserverOpen e W
    let Omega := fun nu => O ∩ kappa ⁻¹' primary nu
    let U := fun nu beta => O ∩ kappa ⁻¹' (g.chart nu beta).source
    let R := fun nu => S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff nu)
    let Rloc := fun nu beta => R nu ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta nu beta z*g.cutoff nu z)
    let Sloc := fun nu beta => (g.chart nu beta ∘ kappa) '' Rloc nu beta
    IsOpen O ∧ ContinuousOn kappa O ∧ MapsTo kappa O W ∧
    (∀ nu, IsOpen (Omega nu) ∧ R nu ⊆ Omega nu ∧ ContinuousOn kappa (Omega nu) ∧
      MapsTo kappa (Omega nu) (W ∩ primary nu)) ∧
    (∀ nu beta, IsOpen (U nu beta) ∧
      (Omega nu ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
        (fun z => g.eta nu beta z*g.cutoff nu z)) ⊆ U nu beta ∧
      MapsTo kappa (U nu beta) (g.chart nu beta).source ∧
      ContDiffOn ℝ ∞ (g.chart nu beta ∘ kappa) (U nu beta) ∧
      Sloc nu beta ⊆ (g.chart nu beta).target ∧
      MapsTo (g.chart nu beta ∘ kappa) (Rloc nu beta) (Sloc nu beta) ∧
      (∀ z ∈ Sloc nu beta, (z.1,g.inverse nu beta z.1 z.2) ∈
        incrementsGlobalRelativeSupport W (g.cutoff nu))) := by
  intro kappa O Omega U R Rloc Sloc
  have hk : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod I) ∞ kappa (univ ×ˢ e.target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (he.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have hO : IsOpen O := hk.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod e.open_target) prim.hW
  have hkO := hk.mono (show O ⊆ univ ×ˢ e.target from inter_subset_left)
  have hmapO : MapsTo kappa O W := fun _ hz => hz.2
  refine ⟨hO,hkO.continuousOn,hmapO,?_,?_⟩
  · intro nu
    have hOm : IsOpen (Omega nu) := hkO.continuousOn.isOpen_inter_preimage hO (prim.hPrimary nu)
    refine ⟨hOm,?_,hkO.continuousOn.mono inter_subset_left,fun _ hz => ⟨hmapO hz.1,hz.2⟩⟩
    intro z hz
    exact ⟨hSO hz.1,prim.hPrimarySupport nu hz.2⟩
  · intro nu beta
    have hU : IsOpen (U nu beta) := hkO.continuousOn.isOpen_inter_preimage hO (g.chart nu beta).open_source
    have hmapU : MapsTo kappa (U nu beta) (g.chart nu beta).source := fun _ hz => hz.2
    have hRsource : MapsTo kappa (Rloc nu beta) (g.chart nu beta).source :=
      fun _ hz => prim.hCombinedSupport nu beta hz.2
    refine ⟨hU,fun _ hz => ⟨hz.1.1,prim.hCombinedSupport nu beta hz.2⟩,hmapU,
      ((prim.hChart nu beta).comp (hkO.mono inter_subset_left) hmapU).contDiffOn,?_,?_,?_⟩
    · rintro z ⟨w,hw,rfl⟩
      exact (g.chart nu beta).map_source (hRsource hw)
    · intro z hz
      exact ⟨z,hz,rfl⟩
    · rintro z ⟨w,hw,rfl⟩
      have ht := (g.chart nu beta).map_source (hRsource hw)
      dsimp only [Function.comp_apply]
      rw [← prim.hInverse nu beta _ ht]
      rw [(g.chart nu beta).left_inv (hRsource hw)]
      exact hw.1.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_raw_observer_domains
