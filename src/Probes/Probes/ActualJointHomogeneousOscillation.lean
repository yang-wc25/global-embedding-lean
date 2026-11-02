import Probes.ActualJointHomogeneousReconstruction
import Probes.ActualSecondaryModulation
import Probes.ActualRealHomogeneousProbe

/-!
# The actual homogeneous real correction with all auxiliary parameters

The function is exactly the earlier original two-channel correction,
now differentiated jointly in every auxiliary parameter and source variable.
The source-to-correction gain tau/ell is retained explicitly. The same
fixed finite polynomial length is used at every observation order.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

def actualJointHomogeneousWaveCost (m N n length j : ℕ) (Mg Mphase : ℝ) : ℝ :=
  euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j Mphase *
    actualJointHomogeneousReconstructionCost m j Mg *
    (‖incrementsModeRealPart (m := m)‖ + ‖incrementsModeImagPart (m := m)‖) *
    ∑ a ∈ Finset.range length, (2 * 2^n * Mg)^a

theorem actualJointHomogeneousWaveCost_nonneg (m N n length j : ℕ) {Mg : ℝ}
    (hMg : 0 ≤ Mg) (Mphase : ℝ) :
    0 ≤ actualJointHomogeneousWaveCost m N n length j Mg Mphase := by
  have hcoord := euclideanTargetCoordinateCost_nonneg N
  have hphase := (incrementsFastMultiplierConstant_pos j Mphase).le
  have hrec := actualJointHomogeneousReconstructionCost_nonneg m j hMg
  unfold actualJointHomogeneousWaveCost
  positivity

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

theorem actual_joint_homogeneous_wave_slow_correction
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (c : Ep → D → M) (source : X → Cdata) (phase : X → ℝ)
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
    (hsource : ContDiffOn ℝ ∞ source O) (hphase : ContDiffOn ℝ ∞ phase O)
    (tau ell Mg Ks Mphase : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
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
    (hsb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k source z‖ ≤ Ks)
    (hpb : ∀ k < j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ (k+1) phase z‖ ≤ Mphase) :
    let W := fun z : X => actualRealHomogeneousProbe (fun x => phase (z.1,x))
      (F z.1) (hF z.1) (c z.1) tau length (fun x => source (z.1,x)) z.2
    ContDiffOn ℝ ∞ W O ∧
      ∀ k ≤ j, ∀ z ∈ S, tau^k * ‖iteratedFDeriv ℝ k W z‖ ≤
        actualJointHomogeneousWaveCost m N n length j Mg Mphase * (tau/ell) * Ks := by
  dsimp only
  let U := fun p => incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
    (incrementsModeComplexFirstOrderB (F p) (hF p) (c p)) ((tau : ℂ)/Complex.I) length
    (fun x => source (p,x))
  let R := fun (channel : Cdata →L[ℝ] D) (z : X) =>
    incrementsModeReconstruction (F z.1) (hF z.1) (c z.1) (channel ∘ U z.1) z.2
  let Profile := ∑ a ∈ Finset.range length, (2 * 2^n * Mg)^a
  let CR := actualJointHomogeneousReconstructionCost m j Mg
  let K := fun (channel : Cdata →L[ℝ] D) => CR * ‖channel‖ * tau * Ks * Profile / ell
  have hell : 0 < ell := htau.trans_le htaul
  have hCR : 0 ≤ CR := actualJointHomogeneousReconstructionCost_nonneg m j hMg
  have hP : 0 ≤ Profile := by unfold Profile; positivity
  have hK : ∀ channel, 0 ≤ K channel := by intro channel; unfold K; positivity
  have hR (channel : Cdata →L[ℝ] D) : ContDiffOn ℝ ∞ (R channel) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k (R channel) z‖ ≤ K channel := by
    obtain ⟨_,hc,hb⟩ := actual_joint_finite_channel_reconstruction F hF c source channel
      n length j horder O S hO hSO hA hB hG hJ hT hsource tau ell Mg Ks
      htau htaul hell1 hMg hKs hAb hBb hGb hJb hTb hsb
    refine ⟨hc,?_⟩
    intro k hk z hz
    apply (le_div_iff₀ hell).mpr
    calc
      (ell^k * ‖iteratedFDeriv ℝ k (R channel) z‖) * ell =
          ell^(k+1) * ‖iteratedFDeriv ℝ k (R channel) z‖ := by rw [pow_succ]; ring
      _ ≤ _ := hb k hk z hz
  have hW := actualSecondaryModulation_contDiffOn phase tau (R incrementsModeRealPart)
    (R incrementsModeImagPart) O hphase (hR _).1 (hR _).1
  have heq : (fun z : X => actualRealHomogeneousProbe (fun x => phase (z.1,x))
      (F z.1) (hF z.1) (c z.1) tau length (fun x => source (z.1,x)) z.2) =
      actualSecondaryModulation phase tau (R incrementsModeRealPart) (R incrementsModeImagPart) := rfl
  rw [heq]
  refine ⟨hW,?_⟩
  have hb := actualSecondaryModulation_weighted_jets j phase (R incrementsModeRealPart)
    (R incrementsModeImagPart) O S hO hSO hphase (hR _).1 (hR _).1
    tau ell Mphase (K incrementsModeRealPart) (K incrementsModeImagPart) htau htaul hell1
    (hK _) (hK _) hpb (hR _).2 (hR _).2
  intro k hk z hz
  apply (hb k hk z hz).trans_eq
  dsimp only [K,CR,Profile,actualJointHomogeneousWaveCost]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_homogeneous_wave_slow_correction
