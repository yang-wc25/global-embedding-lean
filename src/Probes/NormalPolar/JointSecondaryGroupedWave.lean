import NormalPolar.JointSecondaryGroupedProfiles
import Mathlib.Data.Finset.Sigma

/-! Linear full-wave jets of the actual grouped reconstruction. The original
primary overlap L and subordinate overlap R give the actual active-piece
count L*R. The temporary dependent sum is used only for this linear norm
estimate; the resulting physical wave still has the original labels and
embedding, and later quadratic extraction groups amplitudes first.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem jointGrouped_active_piece_count
    {P Label : Type*} [Fintype Label]
    {Sub : Label → Type*} [∀ l, Fintype (Sub l)]
    (K : Label → Set P) (pieceK : (l : Label) → Sub l → Set P)
    (hsub : ∀ l s, pieceK l s ⊆ K l) (z : P) (L R : ℕ)
    (hL : (Finset.univ.filter (fun l => z ∈ K l)).card ≤ L)
    (hR : ∀ l, (Finset.univ.filter (fun s => z ∈ pieceK l s)).card ≤ R) :
    (Finset.univ.filter (fun t : Sigma Sub => z ∈ pieceK t.1 t.2)).card ≤ L*R := by
  rw [← Finset.univ_sigma_univ,Finset.filter_sigma,Finset.card_sigma]
  have hs : (∑ l, (Finset.univ.filter (fun s => z ∈ pieceK l s)).card) =
      ∑ l ∈ Finset.univ.filter (fun l => z ∈ K l),
        (Finset.univ.filter (fun s => z ∈ pieceK l s)).card := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro l _ hl
    have hn : z ∉ K l := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hl
    have he : Finset.univ.filter (fun s : Sub l => z ∈ pieceK l s) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s _ hs
      exact hn (hsub l s hs)
    rw [he,Finset.card_empty]
  rw [hs]
  calc
    _ ≤ ∑ _l ∈ Finset.univ.filter (fun l => z ∈ K l), R :=
      Finset.sum_le_sum (fun l _ => hR l)
    _ = (Finset.univ.filter (fun l => z ∈ K l)).card*R := by simp
    _ ≤ L*R := Nat.mul_le_mul_right R hL

variable {E H M Ep Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem jointGrouped_prescribed_wave_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (chi : (l : Fin r) → Sub l → X → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (pieceK : (l : Fin r) → Sub l → Set (Ep × M))
    (hW : IsOpen W) (hsub : ∀ l s, pieceK l s ⊆ K l)
    (n length j : ℕ) (horder : j+1+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu rho : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hrho : 0 ≤ rho)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK n j ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (L R : ℕ)
    (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (hR : ∀ l y, y ∈ S → (Finset.univ.filter (fun s => kappa y ∈ pieceK l s)).card ≤ R)
    (u : Fin p → ℝ) (hu : ‖u‖ ≤ rho) :
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let CR := actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho false
    let CI := actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho true
    let C := actualFinitePrimaryJetConstant (L*R) N j Mphase CR CI
    let wave := jointGroupedPrescribedWave label F hF c vf phase tau length a u ∘ kappa
    ContDiffOn ℝ ∞ wave Omega ∧ ∀ k ≤ j, ∀ y ∈ S,
      tau^k*‖iteratedFDeriv ℝ k wave y‖ ≤ C*delta*tau := by
  intro vf CR CI C wave
  let amp := fun ch l s => round4PrescribedGlobalAmplitude ch label l F hF (c l s) (vf l s) tau length (a l s) u
  have hamplitude (ch : Bool) (l : Fin r) (s : Sub l) := actual_prescribed_amplitude_from_raw
    ch label l F hF (c l s) (chi l s) (nu l s) (a l s) W (pieceK l s) hW n length j horder
    tau ell delta (weight l) Mg Bchi Bnu htau htaul hell1 hMg hdelta hBchi hBnu
    (profiles.raw l s) kappa (profiles.domains l s) (S ∩ kappa ⁻¹' pieceK l s) (profiles.domains_open l s)
    (fun y hy => profiles.active_domain l s ⟨hS hy.1,hy.2⟩) (profiles.source l s)
    (profiles.transition_smooth l s) (profiles.sample l s) T hT (profiles.transition_jets l s) u
  have hcost (ch : Bool) : 0 ≤ actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho ch :=
    actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu rho ch hT hMg hBchi hBnu hrho
  have hbound (ch : Bool) (l : Fin r) (s : Sub l) (k : ℕ) (hk : k ≤ j) (y : Y)
      (hy : y ∈ S ∩ kappa ⁻¹' pieceK l s) :
      ell^k*‖iteratedFDeriv ℝ k (amp ch l s ∘ kappa) y‖ ≤
        actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho ch * delta * tau := by
    let Cl := round4ObservationJetCost T j * round4PrescribedAmplitudeJetCost m N n length j ch (weight l) Mg Bchi Bnu
    have hCl : 0 ≤ Cl := mul_nonneg (round4ObservationJetCost_nonneg T hT j)
      (round4PrescribedAmplitudeJetCost_nonneg m N n length j ch (weight l) hMg hBchi hBnu)
    have hsum : Cl*rho ≤ actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho ch := by
      dsimp only [Cl,actualPrescribedRawAmplitudeCost]
      apply Finset.single_le_sum (f := fun q : Fin r => round4ObservationJetCost T j *
        round4PrescribedAmplitudeJetCost m N n length j ch (weight q) Mg Bchi Bnu * rho)
        (fun l _ => ?_) (Finset.mem_univ l)
      exact mul_nonneg (mul_nonneg (round4ObservationJetCost_nonneg T hT j)
        (round4PrescribedAmplitudeJetCost_nonneg m N n length j ch (weight l) hMg hBchi hBnu)) hrho
    calc
      _ ≤ Cl*delta*tau*‖u‖ := (hamplitude ch l s).2.2 k hk y hy
      _ ≤ Cl*delta*tau*rho := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = (Cl*rho)*delta*tau := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hdelta) htau.le
  have hcount (y : Y) (hy : y ∈ S) :
      (Finset.univ.filter (fun t : Sigma Sub => kappa y ∈ pieceK t.1 t.2)).card ≤ L*R :=
    jointGrouped_active_piece_count K pieceK hsub (kappa y) L R (hL y hy) (fun l => hR l y hy)
  have hout := actual_supported_primary_array_weighted_jets j
    (fun t : Sigma Sub => phase t.1) (fun t => amp false t.1 t.2) (fun t => amp true t.1 t.2)
    W hW (fun t => pieceK t.1 t.2)
    (fun t => (hamplitude false t.1 t.2).1) (fun t => (hamplitude true t.1 t.2).1)
    kappa Omega S hOmega hS hkappa hmap (fun t => profiles.domains t.1 t.2)
    (fun t => profiles.domains_open t.1 t.2) (fun t => profiles.active_domain t.1 t.2)
    (fun t => profiles.phase_smooth t.1 t.2)
    (fun t => (hamplitude false t.1 t.2).2.1) (fun t => (hamplitude true t.1 t.2).2.1)
    (L*R) hcount tau ell delta Mphase CR CI htau htaul hell1 hdelta
    (hcost false) (hcost true) (fun t => profiles.phase_jets t.1 t.2)
    (fun t => hbound false t.1 t.2) (fun t => hbound true t.1 t.2)
  have he : (fun y => ∑ t : Sigma Sub,
      (Real.cos (phase t.1 (kappa y)/tau) • amp false t.1 t.2 (kappa y) -
        Real.sin (phase t.1 (kappa y)/tau) • amp true t.1 t.2 (kappa y))) = wave := by
    funext y
    rw [Fintype.sum_sigma]
    exact (jointGroupedPrescribedWave_eq_piece_sum label F hF c vf phase tau length a u (kappa y)).symm
  rw [he] at hout
  exact hout

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGrouped_active_piece_count
#print axioms GlobalEmbedding.Continuation.jointGrouped_prescribed_wave_from_raw
