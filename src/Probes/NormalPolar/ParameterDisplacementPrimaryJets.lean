import Probes.Round4ParameterProbeCombinedSecondary
import Probes.ActualSecondaryModulation

/-!
# Actual common primary-array jets from both reconstructed channels

The input profiles concern the literal real and imaginary amplitudes and
original phase of each mode. The full trigonometric primary wave is proved
from those profiles. Background and prescribed labels remain distinct in
the same Sum array; no mode, reconstruction channel or phase is replaced.
The coefficient includes the fixed number of supplied primary modes.
-/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

/-- Fixed finite-array cost, chosen before the actual scale and fields. -/
def actualFinitePrimaryJetConstant (count N j : ℕ) (Mphase KR KI : ℝ) : ℝ :=
  (count : ℝ) * euclideanTargetCoordinateCost N *
    incrementsFastMultiplierConstant j Mphase * (KR + KI)

theorem actualFinitePrimaryJetConstant_nonneg (count N j : ℕ)
    (Mphase : ℝ) {KR KI : ℝ} (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) :
    0 ≤ actualFinitePrimaryJetConstant count N j Mphase KR KI := by
  unfold actualFinitePrimaryJetConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg count)
    (euclideanTargetCoordinateCost_nonneg N))
    (incrementsFastMultiplierConstant_pos j Mphase).le) (add_nonneg hKR hKI)

/-- Real two-channel modulation and the actual finite sum produce all
weighted jets; there is no premise estimating the completed primary wave. -/
theorem actual_primary_array_weighted_jets
    {X Label : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype Label]
    {N : ℕ} (j : ℕ) (phase : Label → X → ℝ)
    (R I : Label → X → EuclideanSpace ℝ (Fin N))
    (Omega S : Set X) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hphase : ∀ l, ContDiffOn ℝ ∞ (phase l) Omega)
    (hR : ∀ l, ContDiffOn ℝ ∞ (R l) Omega)
    (hI : ∀ l, ContDiffOn ℝ ∞ (I l) Omega)
    (tau ell delta Mphase KR KI : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI)
    (hpb : ∀ l k, k < j → ∀ z ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ (k + 1) (phase l) z‖ ≤ Mphase)
    (hRb : ∀ l k, k ≤ j → ∀ z ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (R l) z‖ ≤ KR * delta * tau)
    (hIb : ∀ l k, k ≤ j → ∀ z ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (I l) z‖ ≤ KI * delta * tau) :
    let U := fun z => ∑ l, (Real.cos (phase l z / tau) • R l z -
      Real.sin (phase l z / tau) • I l z)
    ContDiffOn ℝ ∞ U Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      tau ^ k * ‖iteratedFDeriv ℝ k U z‖ ≤
        actualFinitePrimaryJetConstant (Fintype.card Label) N j Mphase KR KI * delta * tau := by
  intro U
  let modes : Label → X → EuclideanSpace ℝ (Fin N) :=
    fun l => actualSecondaryModulation (phase l) tau (R l) (I l)
  have hreg (l) : ContDiffOn ℝ ∞ (modes l) Omega :=
    actualSecondaryModulation_contDiffOn (phase l) tau (R l) (I l) Omega
      (hphase l) (hR l) (hI l)
  have hbound (l) : ∀ k ≤ j, ∀ z ∈ S,
      tau ^ k * ‖iteratedFDeriv ℝ k (modes l) z‖ ≤
        euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j Mphase *
          (KR + KI) * delta * tau := by
    have h := actualSecondaryModulation_weighted_jets j (phase l) (R l) (I l)
      Omega S hOmega hSOmega (hphase l) (hR l) (hI l)
      tau ell Mphase (KR * delta * tau) (KI * delta * tau) htau htaul hell1
      (by positivity) (by positivity) (hpb l) (hRb l) (hIb l)
    intro k hk z hz
    exact (h k hk z hz).trans_eq (by ring)
  have hU : U = fun z => ∑ l, modes l z := rfl
  rw [hU]
  refine ⟨ContDiffOn.sum (fun l _ => hreg l), ?_⟩
  intro k hk z hz
  rw [iteratedFDeriv_fun_sum_apply
    (fun l _ => ((hreg l).contDiffAt (hOmega.mem_nhds (hSOmega hz))).of_le (by simp))]
  calc
    _ ≤ tau ^ k * ∑ l, ‖iteratedFDeriv ℝ k (modes l) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg htau.le _)
    _ = ∑ l, tau ^ k * ‖iteratedFDeriv ℝ k (modes l) z‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _ : Label, euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j Mphase *
        (KR + KI) * delta * tau := Finset.sum_le_sum (fun l _ => hbound l k hk z hz)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold actualFinitePrimaryJetConstant
      ring

variable {m N p r : ℕ} {Ep M Λ Β : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

/-- Specialization to the true combined primary in the same global field
used by the complete mixed-secondary construction. The actual amplitudes
retain all homogeneous corrections supplied by the finite solver. -/
theorem actual_combined_primary_weighted_jets
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Fin p → ℝ)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (j : ℕ) (tau ell delta Mphase KR KI : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hKR : 0 ≤ KR) (hKI : 0 ≤ KI) :
    let phi := fun l => Sum.elim g.phase phase l ∘ kappa
    let R := fun l => round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u false l ∘ kappa
    let I := fun l => round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u true l ∘ kappa
    (∀ l, ContDiffOn ℝ ∞ (phi l) Omega) →
    (∀ l, ContDiffOn ℝ ∞ (R l) Omega) → (∀ l, ContDiffOn ℝ ∞ (I l) Omega) →
    (∀ l k, k < j → ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ (k+1) (phi l) z‖ ≤ Mphase) →
    (∀ l k, k ≤ j → ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k (R l) z‖ ≤ KR * delta * tau) →
    (∀ l k, k ≤ j → ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k (I l) z‖ ≤ KI * delta * tau) →
    let U := round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a input u ∘ kappa
    ContDiffOn ℝ ∞ U Omega ∧ ∀ k ≤ j, ∀ z ∈ S,
      tau ^ k * ‖iteratedFDeriv ℝ k U z‖ ≤
        actualFinitePrimaryJetConstant (Fintype.card (Λ ⊕ Fin r)) N j Mphase KR KI * delta * tau := by
  intro phi R I hphase hR hI hpb hRb hIb U
  exact actual_primary_array_weighted_jets j phi R I Omega S hOmega hSOmega
    hphase hR hI tau ell delta Mphase KR KI htau htaul hell1 hdelta hKR hKI hpb hRb hIb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_array_weighted_jets
#print axioms GlobalEmbedding.Continuation.actual_combined_primary_weighted_jets
