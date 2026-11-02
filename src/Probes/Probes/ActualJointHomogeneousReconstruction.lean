import Probes.ActualSecondaryJointReconstruction
import GlobalEmbedding.Paper.IncrementsModeJointQuantitativeFiniteU
import Probes.ActualJointFiniteResidual

/-!
# Actual homogeneous reconstruction in every joint parameter/source direction

The source is fed to the unchanged original finite mode polynomial. Its
actual real or imaginary channel is reconstructed by the original R. The
source is allowed to depend on all auxiliary parameters; none is frozen.
The explicit estimate retains the extra tau from the finite polynomial and
the one slow-derivative loss in reconstruction.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

def actualJointHomogeneousReconstructionCost (m j : ℕ) (Mg : ℝ) : ℝ :=
  2^j * Mg + 2 * 2^(j+j) * Mg * max Mg ‖incrementsModeTransverseJet (m := m)‖

theorem actualJointHomogeneousReconstructionCost_nonneg (m j : ℕ) {Mg : ℝ}
    (hMg : 0 ≤ Mg) : 0 ≤ actualJointHomogeneousReconstructionCost m j Mg := by
  unfold actualJointHomogeneousReconstructionCost
  positivity

/-- Every real-linear observation of the same finite solution has a genuine
joint reconstructed field. The only estimates assumed are on the original
coefficients and source, not the solution or reconstructed correction. -/
theorem actual_joint_finite_channel_reconstruction
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (c : Ep → D → M) (source : X → Cdata) (channel : Cdata →L[ℝ] D)
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
    (hsource : ContDiffOn ℝ ∞ source O)
    (tau ell Mg Ks : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKs : 0 ≤ Ks)
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
    (hsb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k source z‖ ≤ Ks) :
    let U := fun p => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
      (incrementsModeComplexFirstOrderB (F p) (hF p) (c p)) ((tau : ℂ)/Complex.I) length
      (fun x => source (p,x))
    let R := fun z : X => incrementsModeReconstruction (F z.1) (hF z.1) (c z.1)
      (channel ∘ U z.1) z.2
    let Profile := ∑ a ∈ Finset.range length, (2 * 2^n * Mg)^a
    ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) O ∧
      ContDiffOn ℝ ∞ R O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k R z‖ ≤
        actualJointHomogeneousReconstructionCost m j Mg * ‖channel‖ * tau * Ks * Profile := by
  dsimp only
  let U := fun p => incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
    (incrementsModeComplexFirstOrderB (F p) (hF p) (c p)) ((tau : ℂ)/Complex.I) length
    (fun x => source (p,x))
  let Uj := fun z : X => U z.1 z.2
  let Profile := ∑ a ∈ Finset.range length, (2 * 2^n * Mg)^a
  have hell : 0 < ell := htau.trans_le htaul
  obtain ⟨_,hU,hUb⟩ := incrementsModeJointFiniteU_compatible_contDiffOn_scaled_jet
    F hF c source n length O S hO hSO hA hB hsource tau ell Mg Ks
    htau hell hell1 hMg hKs hAb hBb hsb
  have hP : 0 ≤ Profile := by unfold Profile; positivity
  have hRatio : (∑ a ∈ Finset.range length, ((2 * 2^n * Mg) * tau / ell)^a) ≤ Profile := by
    apply Finset.sum_le_sum
    intro a ha
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hell).mpr
    exact mul_le_mul_of_nonneg_left htaul (by positivity)
  have hUbound : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k Uj z‖ ≤ tau * Ks * Profile := by
    intro k hk z hz
    exact (hUb k (by omega) z hz).trans
      (mul_le_mul_of_nonneg_left hRatio (mul_nonneg htau.le hKs))
  have hchannel : ContDiffOn ℝ ∞ (channel ∘ Uj) O := channel.contDiff.comp_contDiffOn hU
  have hchannelBound : ∀ k ≤ j+1, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ k (channel ∘ Uj) z‖ ≤ ‖channel‖ * (tau * Ks * Profile) := by
    intro k hk z hz
    exact slow_linear_jet_bound channel O hO Uj hU k ell (tau * Ks * Profile)
      hell.le z (hSO hz) (hUbound k hk z hz)
  obtain ⟨hR,hRb⟩ := actual_joint_reconstruction_slow_jets F hF c (channel ∘ Uj) j O S hO hSO
    hG hJ hT hchannel ell Mg (‖channel‖ * (tau * Ks * Profile)) hell hell1 hMg
    (by positivity) hGb hJb hTb hchannelBound
  refine ⟨hU,hR,?_⟩
  intro k hk z hz
  simpa only [Uj,U,Profile,Function.comp_def,actualJointHomogeneousReconstructionCost,mul_assoc]
    using hRb k hk z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_finite_channel_reconstruction
