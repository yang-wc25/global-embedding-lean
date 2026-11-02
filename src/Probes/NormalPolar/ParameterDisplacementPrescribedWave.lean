import NormalPolar.ParameterDisplacementPrescribedRaw
import Probes.Round4PrescribedGlobalWave

/-!
# Complete prescribed wave jets from the same primitive source

Every amplitude is produced by the finite reconstruction from the actual
normal source. The phase is used only on its active carrier. The sum uses the
actual overlap count, and the constant is fixed before the probe parameter.
-/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualPrescribedRawAmplitudeCost (m N n length j : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu rho : ℝ) (imag : Bool) : ℝ :=
  ∑ l, (round4ObservationJetCost T j *
    round4PrescribedAmplitudeJetCost m N n length j imag (weight l) Mg Bchi Bnu) * rho

theorem actualPrescribedRawAmplitudeCost_nonneg (m N n length j : ℕ)
    (T : ℕ → ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu rho : ℝ) (imag : Bool)
    (hT : ∀ k, 0 ≤ T k) (hMg : 0 ≤ Mg) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hrho : 0 ≤ rho) :
    0 ≤ actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho imag := by
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mul_nonneg (round4ObservationJetCost_nonneg T hT j)
    (round4PrescribedAmplitudeJetCost_nonneg m N n length j imag (weight l) hMg hBchi hBnu)) hrho

/-- Actual primitive geometry together with its observation on the active
carrier. There are no reconstructed amplitude or full-wave estimate fields. -/
structure ActualPrescribedObservationProfiles
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ)
    (kappa : Y → Ep × M) (Omega S : Set Y) (T : ℕ → ℝ)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ) where
  raw : ∀ l, ActualPrescribedSpatialRawProfiles F hF (c l) (chi l) (nu l) (a l) W (K l) n j ell Mg Bchi Bnu
  domains : Fin r → Set Y
  domains_open : ∀ l, IsOpen (domains l)
  active_domain : ∀ l, Omega ∩ kappa ⁻¹' K l ⊆ domains l
  source : ∀ l, MapsTo kappa (domains l) (a l).source
  transition_smooth : ∀ l, ContDiffOn ℝ ∞ (a l ∘ kappa) (domains l)
  sample : ∀ l y, y ∈ S ∩ kappa ⁻¹' K l → a l (kappa y) ∈ (raw l).sample
  transition_jets : ∀ l k, 1 ≤ k → k ≤ j → ∀ y ∈ S ∩ kappa ⁻¹' K l,
    ell^(k-1)*‖iteratedFDeriv ℝ k (a l ∘ kappa) y‖ ≤ T k
  phase_smooth : ∀ l, ContDiffOn ℝ ∞ (phase l ∘ kappa) (domains l)
  phase_jets : ∀ l k, k < j → ∀ y ∈ S ∩ kappa ⁻¹' K l,
    ell^k*‖iteratedFDeriv ℝ (k+1) (phase l ∘ kappa) y‖ ≤ Mphase

/-- The complete actual prescribed sum, including both reconstruction
channels and all lower derivatives, follows from primitive raw profiles. -/
theorem actual_prescribed_wave_from_raw
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (W : Set (Ep × M)) (K : Fin r → Set (Ep × M))
    (hW : IsOpen W) (n length j : ℕ) (horder : j+1+length ≤ n)
    (tau ell delta : ℝ) (weight : Fin r → ℝ) (Mg Bchi Bnu rho : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hrho : 0 ≤ rho)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (phase : Fin r → Ep × M → ℝ) (Mphase : ℝ)
    (profiles : ActualPrescribedObservationProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu
      kappa Omega S T phase Mphase)
    (L : ℕ) (hL : ∀ y ∈ S, (Finset.univ.filter (fun l => kappa y ∈ K l)).card ≤ L)
    (u : Fin p → ℝ) (hu : ‖u‖ ≤ rho) :
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let CR := actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho false
    let CI := actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho true
    let C := actualFinitePrimaryJetConstant L N j Mphase CR CI
    let wave := round4PrescribedGlobalWave label F hF c vf phase tau length a u ∘ kappa
    ContDiffOn ℝ ∞ wave Omega ∧ ∀ k ≤ j, ∀ y ∈ S,
      tau^k*‖iteratedFDeriv ℝ k wave y‖ ≤ C*delta*tau := by
  intro vf CR CI C wave
  let amp := fun ch l => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) u
  have hamplitude (ch : Bool) (l : Fin r) := actual_prescribed_amplitude_from_raw
    ch label l F hF (c l) (chi l) (nu l) (a l) W (K l) hW n length j horder
    tau ell delta (weight l) Mg Bchi Bnu htau htaul hell1 hMg hdelta hBchi hBnu
    (profiles.raw l) kappa (profiles.domains l) (S ∩ kappa ⁻¹' K l) (profiles.domains_open l)
    (fun y hy => profiles.active_domain l ⟨hS hy.1,hy.2⟩) (profiles.source l)
    (profiles.transition_smooth l) (profiles.sample l) T hT (profiles.transition_jets l) u
  have hcost (ch : Bool) : 0 ≤ actualPrescribedRawAmplitudeCost m N n length j T weight Mg Bchi Bnu rho ch :=
    actualPrescribedRawAmplitudeCost_nonneg m N n length j T weight Mg Bchi Bnu rho ch hT hMg hBchi hBnu hrho
  have hbound (ch : Bool) (l : Fin r) (k : ℕ) (hk : k ≤ j) (y : Y) (hy : y ∈ S ∩ kappa ⁻¹' K l) :
      ell^k*‖iteratedFDeriv ℝ k (amp ch l ∘ kappa) y‖ ≤
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
      _ ≤ Cl*delta*tau*‖u‖ := (hamplitude ch l).2.2 k hk y hy
      _ ≤ Cl*delta*tau*rho := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = (Cl*rho)*delta*tau := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hdelta) htau.le
  exact actual_supported_primary_array_weighted_jets j phase (amp false) (amp true)
    W hW K (fun l => (hamplitude false l).1) (fun l => (hamplitude true l).1)
    kappa Omega S hOmega hS hkappa hmap profiles.domains profiles.domains_open
    profiles.active_domain profiles.phase_smooth (fun l => (hamplitude false l).2.1)
    (fun l => (hamplitude true l).2.1) L hL tau ell delta Mphase CR CI htau htaul hell1 hdelta
    (hcost false) (hcost true) profiles.phase_jets (hbound false) (hbound true)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_prescribed_wave_from_raw
