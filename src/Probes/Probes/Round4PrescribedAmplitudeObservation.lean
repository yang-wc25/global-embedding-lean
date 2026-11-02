import Probes.Round4PrescribedAmplitudeJets
import Probes.Round4PrescribedGlobalParity
import Probes.ActualJointChartTransfer

/-!
# Complete prescribed amplitudes through their actual joint chart transition

Primitive source/cutoff/normal profiles are first consumed by the original
finite reconstruction. The literal global extension is then observed through
its actual chart transition, retaining every auxiliary parameter direction.
Constants use a finite transition-jet prefix and have no scale or atlas count.
This is the active-chart quantitative bridge; inactive pieces have zero germs.
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
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

def round4ObservationJetCost (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), actualFastChartTransferCost T k

theorem round4ObservationJetCost_nonneg (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (j : ℕ) :
    0 ≤ round4ObservationJetCost T j := by
  exact Finset.sum_nonneg (fun k _ => actualFastChartTransferCost_nonneg T hT k)

theorem round4_prescribed_global_amplitude_observation_jets
    (imag : Bool) (label : (Fin r × Bool) ↪ Fin p) (l : Fin r)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)) (c : Ep → D → M)
    (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x))
    (n length j : ℕ) (horder : j+1+length ≤ n)
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
    (hGb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
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
    (htransitionb : ∀ k, 1 ≤ k → k ≤ j → ∀ y ∈ Sobs,
      ell^(k-1)*‖iteratedFDeriv ℝ k (a ∘ kappa) y‖ ≤ T k) :
    let vf := actualProbeNormalAmplitude F c chi nu delta tau lam
    let amp := fun u y => round4PrescribedGlobalAmplitude imag label l F hF c vf tau length a u (kappa y)
    let C := round4ObservationJetCost T j * round4PrescribedAmplitudeJetCost m N n length j imag lam Mg Bchi Bnu
    ∀ u, ContDiffOn ℝ ∞ (amp u) Omega ∧ ∀ k ≤ j, ∀ y ∈ Sobs,
      ell^k*‖iteratedFDeriv ℝ k (amp u) y‖ ≤ C*delta*tau*‖u‖ := by
  intro vf amp C u
  have hell : 0 < ell := htau.trans_le htaul
  have hlocal := round4_prescribed_amplitude_all_weighted_jets imag label l F hF c chi nu
    n length j horder O S hO hSO hA hB hG hJ hT hBR hchi hnu tau ell delta lam Mg Bchi Bnu
    htau htaul hell1 hMg hdelta hBchi hBnu hAb hBb hGb hJb hTb hBRb hchib hnub u
  let Alocal := fun z : X => round4PrescribedAmplitude imag label l (F z.1) (hF z.1)
    (c z.1) (vf z.1) tau length u z.2
  let Clocal := round4PrescribedAmplitudeJetCost m N n length j imag lam Mg Bchi Bnu
  have he : EqOn (amp u) (Alocal ∘ (a ∘ kappa)) Omega := by
    intro y hy
    simp only [amp,round4PrescribedGlobalAmplitude,if_pos (hsource hy)]
    rfl
  have hmap : MapsTo (a ∘ kappa) Omega O := fun y hy => haO (a.map_source (hsource hy))
  refine ⟨(hlocal.1.comp htransition hmap).congr he,?_⟩
  intro k hk y hy
  have hg : amp u =ᶠ[𝓝 y] Alocal ∘ (a ∘ kappa) :=
    he.eventuallyEq_of_mem (hOmega.mem_nhds (hSobs hy))
  rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
  have hb := actual_fast_joint_chart_transfer T hTprof k (a ∘ kappa) Alocal Omega O
    hOmega hO htransition hlocal.1 hmap y (hSobs hy) ell ell (Clocal*delta*tau*‖u‖)
    hell le_rfl (fun q hq => hlocal.2 q (hq.trans hk) _ (hsample y hy))
    (fun q hq hqk => htransitionb q hq (hqk.trans hk) y hy)
  have hprefix : actualFastChartTransferCost T k ≤ round4ObservationJetCost T j := by
    exact Finset.single_le_sum (fun q _ => actualFastChartTransferCost_nonneg T hTprof q)
      (by simpa using hk)
  have hClocal := round4PrescribedAmplitudeJetCost_nonneg m N n length j imag lam hMg hBchi hBnu
  exact hb.trans ((mul_le_mul_of_nonneg_right hprefix (show 0 ≤ Clocal*delta*tau*‖u‖ by
    dsimp only [Clocal]; positivity)).trans_eq (by dsimp only [C,Clocal]; ring))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_amplitude_observation_jets
