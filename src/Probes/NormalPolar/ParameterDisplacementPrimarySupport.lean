import NormalPolar.ParameterDisplacementPrimaryJets
import Probes.ActualIncrementPrimaryObservationSum

/-!
# Actual primary jets with only carrier-local phase regularity

The original phases can be arbitrary off their own active carriers. Real
amplitude support yields zero germs there before differentiation. The actual
relative-support summation keeps the active primary count, not the total
number of labels. Both reconstructed real channels are retained.
-/

noncomputable section
open Set Filter Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

/-- Local phase/amplitude profiles and actual relative supports produce the
whole primary array and its derivatives. No inactive-phase hypothesis occurs. -/
theorem actual_supported_primary_array_weighted_jets
    {P Y Label : Type*} [TopologicalSpace P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype Label]
    {N : ℕ} (j : ℕ) (phase : Label → P → ℝ)
    (ZR ZI : Label → P → EuclideanSpace ℝ (Fin N))
    (W : Set P) (hW : IsOpen W) (K : Label → Set P)
    (hRsupport : ∀ l, tsupport (fun z : W => ZR l z) ⊆ Subtype.val ⁻¹' K l)
    (hIsupport : ∀ l, tsupport (fun z : W => ZI l z) ⊆ Subtype.val ⁻¹' K l)
    (kappa : Y → P) (Omega S : Set Y) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : Label → Set Y) (hO : ∀ l, IsOpen (O l))
    (hcover : ∀ l, Omega ∩ kappa ⁻¹' K l ⊆ O l)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l ∘ kappa) (O l))
    (hZR : ∀ l, ContDiffOn ℝ ∞ (ZR l ∘ kappa) (O l))
    (hZI : ∀ l, ContDiffOn ℝ ∞ (ZI l ∘ kappa) (O l))
    (L : ℕ) (hL : ∀ z ∈ S, (Finset.univ.filter (fun l => kappa z ∈ K l)).card ≤ L)
    (tau ell delta Mphase KR KI : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI)
    (hpb : ∀ l k, k < j → ∀ z ∈ S ∩ kappa ⁻¹' K l,
      ell ^ k * ‖iteratedFDeriv ℝ (k+1) (phase l ∘ kappa) z‖ ≤ Mphase)
    (hRb : ∀ l k, k ≤ j → ∀ z ∈ S ∩ kappa ⁻¹' K l,
      ell ^ k * ‖iteratedFDeriv ℝ k (ZR l ∘ kappa) z‖ ≤ KR * delta * tau)
    (hIb : ∀ l k, k ≤ j → ∀ z ∈ S ∩ kappa ⁻¹' K l,
      ell ^ k * ‖iteratedFDeriv ℝ k (ZI l ∘ kappa) z‖ ≤ KI * delta * tau) :
    let U := fun z => ∑ l, (Real.cos (phase l (kappa z) / tau) • ZR l (kappa z) -
      Real.sin (phase l (kappa z) / tau) • ZI l (kappa z))
    ContDiffOn ℝ ∞ U Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      tau ^ k * ‖iteratedFDeriv ℝ k U z‖ ≤
        actualFinitePrimaryJetConstant L N j Mphase KR KI * delta * tau := by
  intro U
  let modes : Label → P → EuclideanSpace ℝ (Fin N) := fun l z =>
    Real.cos (phase l z / tau) • ZR l z - Real.sin (phase l z / tau) • ZI l z
  let Cbase := euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j Mphase * (KR+KI)
  have hCbase : 0 ≤ Cbase := mul_nonneg
    (mul_nonneg (euclideanTargetCoordinateCost_nonneg N)
      (incrementsFastMultiplierConstant_pos j Mphase).le) (add_nonneg hKR hKI)
  have hsupp (l : Label) : tsupport (fun z : W => modes l z) ⊆ Subtype.val ⁻¹' K l := by
    have hlocal : tsupport (fun z : W => modes l z) ⊆
        tsupport (fun z : W => ZR l z) ∪ tsupport (fun z : W => ZI l z) := by
      apply closure_minimal _ ((isClosed_tsupport _).union (isClosed_tsupport _))
      intro z hz
      by_contra hn
      have hRzero : ZR l z = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun z : W => ZR l z) (fun hh => hn (Or.inl hh))
      have hIzero : ZI l z = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun z : W => ZI l z) (fun hh => hn (Or.inr hh))
      exact hz (by simp only [modes,hRzero,hIzero,smul_zero,sub_zero])
    exact hlocal.trans (union_subset (hRsupport l) (hIsupport l))
  have hreg (l) : ContDiffOn ℝ ∞ (modes l ∘ kappa) (O l) :=
    actualSecondaryModulation_contDiffOn (phase l ∘ kappa) tau
      (ZR l ∘ kappa) (ZI l ∘ kappa) (O l) (hphase l) (hZR l) (hZI l)
  have hjet (l) : ∀ k ≤ j, ∀ z ∈ S ∩ kappa ⁻¹' K l,
      tau ^ k * ‖iteratedFDeriv ℝ k (modes l ∘ kappa) z‖ ≤ Cbase * delta * tau := by
    have hsub : S ∩ kappa ⁻¹' K l ⊆ O l := fun z hz => hcover l ⟨hSOmega hz.1,hz.2⟩
    have h := actualSecondaryModulation_weighted_jets j (phase l ∘ kappa)
      (ZR l ∘ kappa) (ZI l ∘ kappa) (O l) (S ∩ kappa ⁻¹' K l)
      (hO l) hsub (hphase l) (hZR l) (hZI l)
      tau ell Mphase (KR*delta*tau) (KI*delta*tau) htau htaul hell1
      (by positivity) (by positivity) (hpb l) (hRb l) (hIb l)
    intro k hk z hz
    exact (h k hk z hz).trans_eq (by dsimp only [Cbase]; ring)
  have hcount (l : Label) (z : Y) (_hz : z ∈ S) :
      (Finset.univ.filter (fun _ : Unit => kappa z ∈ K l)).card ≤ 1 :=
    (Finset.card_filter_le _ _).trans_eq (by simp)
  have hsum := actual_primary_observation_sum_weighted_jets
    (fun l (_ : Unit) => modes l) K (fun l (_ : Unit) => K l) (fun _ _ => Subset.rfl)
    W hW (fun l _ => hsupp l) kappa Omega S hOmega hSOmega hkappa hmap
    (fun l (_ : Unit) => O l) (fun l _ => hO l) (fun l _ => hcover l)
    (fun l _ => hreg l) L 1 j hL hcount tau (Cbase*delta*tau) htau (by positivity)
    (fun l _ => hjet l)
  simpa only [Finset.univ_unique,Finset.sum_singleton,Nat.mul_one,
    actualFinitePrimaryJetConstant,Cbase,mul_assoc] using hsum

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_supported_primary_array_weighted_jets
