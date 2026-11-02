import Probes.ActualSecondaryPhysicalJets

/-!
# Remodulating the actual physical secondary error

The real tensor error is the real part of the original fast exponential
times its genuine demodulated physical residual. The fixed real projection
has norm at most one. The adapted coordinate phase is a native norm-one
linear map, so all of its slow derivative bounds are supplied exactly.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

theorem actual_complex_demodulated_residual_real (theta a b : ℝ) (h : ℂ) :
    (Complex.exp ((theta : ℂ) * Complex.I) *
      (Complex.exp (-(theta : ℂ) * Complex.I) * ((a : ℂ) + Complex.I * (b : ℂ)) - h)).re =
      a - (Complex.exp ((theta : ℂ) * Complex.I) * h).re := by
  have he : Complex.exp ((theta : ℂ) * Complex.I) *
      Complex.exp (-(theta : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [mul_sub, ← mul_assoc, he, one_mul, Complex.sub_re]
  simp

variable {m : ℕ}

def actualComplexTensorRealPart :
    (Fin (m + 1) → Fin (m + 1) → ℂ) →L[ℝ] (Fin (m + 1) → Fin (m + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    Complex.reCLM.comp
      ((ContinuousLinearMap.proj j : (Fin (m + 1) → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj i :
          (Fin (m + 1) → Fin (m + 1) → ℂ) →L[ℝ] (Fin (m + 1) → ℂ)))

@[simp] theorem actualComplexTensorRealPart_apply
    (T : Fin (m + 1) → Fin (m + 1) → ℂ) (i j : Fin (m + 1)) :
    actualComplexTensorRealPart T i j = (T i j).re := rfl

theorem actualComplexTensorRealPart_norm_le : ‖actualComplexTensorRealPart (m := m)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg T)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg T)).2
  intro j
  change ‖(T i j).re‖ ≤ ‖T‖
  exact (Complex.abs_re_le_norm _).trans
    ((norm_le_pi_norm (T i) j).trans (norm_le_pi_norm T i))

theorem actual_linear_phase_slow_jets {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : X →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (ell : ℝ) (z : X) (k : ℕ) :
    ell ^ k * ‖iteratedFDeriv ℝ (k + 1) L z‖ ≤ 1 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hder : fderiv ℝ L = fun _ => L := funext fun x => L.fderiv
  rw [hder]
  cases k with
  | zero => simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using hL
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, mul_zero, zero_le_one]

def actualSecondaryCoordinatePhase {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] :
    (Ep × EuclideanSpace ℝ (Fin (m + 1))) →L[ℝ] ℝ :=
  (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ Ep _)

theorem actualSecondaryCoordinatePhase_norm_le
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] :
    ‖actualSecondaryCoordinatePhase (Ep := Ep) (m := m)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z.2 0‖ ≤ 1 * ‖z‖
  exact (PiLp.norm_apply_le z.2 0).trans (by simpa using norm_snd_le z)

/-- All joint fast jets of the literal real remodulated tensor, with no
dimension loss for the complex-to-real tensor projection. -/
theorem actual_real_tensor_remodulation_weighted_jets
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (e : X → Fin (m + 1) → Fin (m + 1) → ℂ) (phase : X → ℝ)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (he : ContDiffOn ℝ ∞ e O) (hphase : ContDiffOn ℝ ∞ phase O)
    (j : ℕ) (tau ell M K : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hK : 0 ≤ K)
    (hp : ∀ k < j, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ (k + 1) phase z‖ ≤ M)
    (heb : ∀ k ≤ j, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k e z‖ ≤ K) :
    let R := fun z i a =>
      (Complex.exp (((phase z / tau : ℝ) : ℂ) * Complex.I) * e z i a).re
    ContDiffOn ℝ ∞ R O ∧
      ∀ r ≤ j, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r R z‖ ≤
        incrementsFastMultiplierConstant j M * K := by
  intro R
  let W := fun z => Complex.exp (Complex.I * ((phase z / tau : ℝ) : ℂ)) • e z
  have hW : ContDiffOn ℝ ∞ W O :=
    (increments_fast_phase_contDiffOn O phase hphase tau).smul he
  have heq : R = actualComplexTensorRealPart ∘ W := by
    funext z i a
    simp only [R, Function.comp_apply, actualComplexTensorRealPart_apply, W,
      Pi.smul_apply, smul_eq_mul, mul_comm Complex.I]
  rw [heq]
  refine ⟨actualComplexTensorRealPart.contDiff.comp_contDiffOn hW, ?_⟩
  intro r hr z hz
  have hw := increments_fast_multiplier_jet_bound j r hr O hO phase e hphase he z (hSO hz)
    tau ell M K htau htaul hell1 hK (fun k hk => hp k hk z hz) (fun k hk => heb k hk z hz)
  have hk : 0 ≤ incrementsFastMultiplierConstant j M * K :=
    mul_nonneg (incrementsFastMultiplierConstant_pos j M).le hK
  exact (slow_linear_jet_bound actualComplexTensorRealPart O hO W hW r tau
    (incrementsFastMultiplierConstant j M * K) htau.le z (hSO hz) hw).trans
      (mul_le_of_le_one_left hk actualComplexTensorRealPart_norm_le)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_complex_demodulated_residual_real
#print axioms GlobalEmbedding.Continuation.actualComplexTensorRealPart_norm_le
#print axioms GlobalEmbedding.Continuation.actual_linear_phase_slow_jets
#print axioms GlobalEmbedding.Continuation.actualSecondaryCoordinatePhase_norm_le
#print axioms GlobalEmbedding.Continuation.actual_real_tensor_remodulation_weighted_jets
