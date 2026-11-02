import Probes.Round4PrescribedAmplitudeObservation
import Probes.Round4ActualProbeCoefficientJets

/-!
# Actual complete observed coefficients, with scale-uniform slow jets

Every mode is transported through its own real source-to-observer transition.
Its complete reconstructed amplitude is differentiated in the observer's true
spatial variable, and its fast phase term is retained. The primitive normal
source supplies a delta*tau factor; the true phase division cancels tau.
No actual coefficient or reconstructed-amplitude budget is a premise.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
variable {Eq : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
local notation "Y" => Eq × (EuclideanSpace ℝ (Fin (m+1)))
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

theorem round4_prescribed_observed_coefficient_all_weighted_jets
    (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (n length j : ℕ) (horder : j+2+length ≤ n)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 a : V)) O)
    (hchi : ContDiffOn ℝ ∞ chi O)
    (hnu : ContDiffOn ℝ ∞ (fun z : X => (nu z.1 z.2 : V)) O)
    (tau ell delta lam Mg Bchi Bnu : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hdelta : 0 ≤ delta) (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hAb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j+1, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ k ≤ n, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun a : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ Mg)
    (hchib : ∀ k ≤ n, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ n, ∀ z ∈ O, ell^k *
      ‖iteratedFDeriv ℝ k (fun w : X => (nu w.1 w.2 : V)) z‖ ≤ Bnu)
    (a : OpenPartialHomeomorph (Ep × M) X) (haO : a.target ⊆ O)
    (kappa : Y → Ep × M) (Omega Sobs : Set Y) (hOmega : IsOpen Omega) (hSobs : Sobs ⊆ Omega)
    (hsource : MapsTo kappa Omega a.source)
    (htransition : ContDiffOn ℝ ∞ (a ∘ kappa) Omega)
    (hsample : ∀ y ∈ Sobs, a (kappa y) ∈ S)
    (T : ℕ → ℝ) (hTprof : ∀ k, 0 ≤ T k)
    (htransitionb : ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ Sobs,
      ell^(k-1)*‖iteratedFDeriv ℝ k (a ∘ kappa) y‖ ≤ T k)
    (phase : Ep × M → ℝ) (v : D) (co : Fin N) (Mp : ℝ) (hMp : 0 ≤ Mp)
    (hphase : ContDiffOn ℝ ∞ (phase ∘ kappa) Omega)
    (hphib : ∀ k ≤ j, ∀ y ∈ Sobs, ell^k*‖iteratedFDeriv ℝ k
      (fun z : Y => fderiv ℝ (fun x => phase (kappa (z.1,x))) z.2 v) y‖ ≤ Mp) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let amp := fun ch u y => round4PrescribedGlobalAmplitude ch label l F hF c vf tau length a u (kappa y)
    let coeff := fun u z => incrementsPrimaryDerivativeCoefficient (fun x => phase (kappa (z.1,x))) tau
      (fun (_ : Unit) _ => 1) (fun _ x => amp false u (z.1,x)) (fun _ x => amp true u (z.1,x)) z.2 v co
    let CR := round4ObservationJetCost T (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) false lam Mg Bchi Bnu
    let CQ := round4ObservationJetCost T (j+1) * round4PrescribedAmplitudeJetCost m N n length (j+1) true lam Mg Bchi Bnu
    let C := round4CompleteCoefficientJetCost j v co CR CQ Mp
    ∀ u, ContDiffOn ℝ ∞ (coeff u) Omega ∧ ∀ k ≤ j, ∀ y ∈ Sobs,
      ell^k*‖iteratedFDeriv ℝ k (coeff u) y‖ ≤ C*delta*‖u‖ := by
  intro vf amp coeff CR CQ C u
  have ha (ch : Bool) := round4_prescribed_global_amplitude_observation_jets ch label l F hF c chi nu
    n length (j+1) (by omega) O S hO hSO hA hB hG hJ hT hBR hchi hnu
    tau ell delta lam Mg Bchi Bnu htau htaul hell1 hMg hdelta hBchi hBnu
    hAb hBb hGb hJb hTb hBRb hchib hnub a haO kappa Omega Sobs hOmega hSobs
    hsource htransition hsample T hTprof htransitionb u
  have hTcost := round4ObservationJetCost_nonneg T hTprof (j+1)
  have hCR : 0 ≤ CR := mul_nonneg hTcost
    (round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) false lam hMg hBchi hBnu)
  have hCQ : 0 ≤ CQ := mul_nonneg hTcost
    (round4PrescribedAmplitudeJetCost_nonneg m N n length (j+1) true lam hMg hBchi hBnu)
  have hc := round4_complete_coefficient_slow_jets (amp false u) (amp true u) (phase ∘ kappa) v co
    Omega Sobs hOmega hSobs (ha false).1 (ha true).1 hphase j tau ell
    (CR*delta*‖u‖) (CQ*delta*‖u‖) Mp htau htaul (by positivity) (by positivity) hMp
    (fun k hk z hz => ((ha false).2 k hk z hz).trans_eq (by ring))
    (fun k hk z hz => ((ha true).2 k hk z hz).trans_eq (by ring)) hphib
  refine ⟨hc.1,?_⟩
  intro k hk z hz
  exact (hc.2 k hk z hz).trans_eq (by dsimp only [C,round4CompleteCoefficientJetCost]; ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_observed_coefficient_all_weighted_jets
