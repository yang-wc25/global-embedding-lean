import Probes.ActualReconstructedOscillation
import Probes.ActualSecondaryMixedJets
import Probes.ActualSecondaryScaleAbsorption

/-!
# The same real secondary displacement and its native parameter Hessian

The secondary displacement is the literal cosine times real channel minus
sine times imaginary channel. The full joint jet estimate, the native mixed
parameter/Hessian estimate and the original-scale absorption all concern
that same function. The actual forcing/reconstruction producer supplies the
two channel profiles in `ActualSecondaryJointQuadratic`.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation

variable {X Ep Es : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  {N : ℕ}

private noncomputable local instance secondaryModBilinearSemi :
    SeminormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance secondaryModBilinearNormed :
    NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance secondaryModBilinearSpace :
    NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance secondaryModResponseSemi :
    SeminormedAddCommGroup (Ep →L[ℝ] Es →L[ℝ] Es →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance secondaryModResponseNormed :
    NormedAddCommGroup (Ep →L[ℝ] Es →L[ℝ] Es →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearMap.toNormedAddCommGroup

def actualSecondaryModulation (phase : X → ℝ) (tau : ℝ)
    (ZR ZI : X → EuclideanSpace ℝ (Fin N)) : X → EuclideanSpace ℝ (Fin N) :=
  fun z => Real.cos (phase z / tau) • ZR z - Real.sin (phase z / tau) • ZI z

theorem actualSecondaryModulation_contDiffOn
    (phase : X → ℝ) (tau : ℝ) (ZR ZI : X → EuclideanSpace ℝ (Fin N)) (O : Set X)
    (hphase : ContDiffOn ℝ ∞ phase O)
    (hZR : ContDiffOn ℝ ∞ ZR O) (hZI : ContDiffOn ℝ ∞ ZI O) :
    ContDiffOn ℝ ∞ (actualSecondaryModulation phase tau ZR ZI) O :=
  ((hphase.div_const tau).cos.smul hZR).sub ((hphase.div_const tau).sin.smul hZI)

/-- The real oscillation creates no support outside the two reconstructed
channels, even at zero phase or zero frequency parameter. -/
theorem actualSecondaryModulation_tsupport
    (phase : X → ℝ) (tau : ℝ) (ZR ZI : X → EuclideanSpace ℝ (Fin N)) :
    tsupport (actualSecondaryModulation phase tau ZR ZI) ⊆ tsupport ZR ∪ tsupport ZI := by
  apply closure_minimal _ ((isClosed_tsupport ZR).union (isClosed_tsupport ZI))
  intro z hz
  by_contra hn
  have hr : ZR z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inl h))
  have hi : ZI z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inr h))
  apply hz
  simp only [actualSecondaryModulation, hr, hi, smul_zero, sub_zero]

/-- Reuse the original fast multiplier on both original real channels.
Every derivative is a native joint derivative of the literal real map. -/
theorem actualSecondaryModulation_weighted_jets
    (j : ℕ) (phase : X → ℝ) (ZR ZI : X → EuclideanSpace ℝ (Fin N))
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hphase : ContDiffOn ℝ ∞ phase O)
    (hZR : ContDiffOn ℝ ∞ ZR O) (hZI : ContDiffOn ℝ ∞ ZI O)
    (tau ell M KR KI : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hKR : 0 ≤ KR) (hKI : 0 ≤ KI)
    (hpb : ∀ a < j, ∀ z ∈ S, ell ^ a * ‖iteratedFDeriv ℝ (a + 1) phase z‖ ≤ M)
    (hRb : ∀ a ≤ j, ∀ z ∈ S, ell ^ a * ‖iteratedFDeriv ℝ a ZR z‖ ≤ KR)
    (hIb : ∀ a ≤ j, ∀ z ∈ S, ell ^ a * ‖iteratedFDeriv ℝ a ZI z‖ ≤ KI) :
    ∀ r ≤ j, ∀ z ∈ S,
      tau ^ r * ‖iteratedFDeriv ℝ r (actualSecondaryModulation phase tau ZR ZI) z‖ ≤
        euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j M * (KR + KI) := by
  have hR := actualTrigModulation_contDiffOn false phase tau ZR O hphase hZR
  have hI := actualTrigModulation_contDiffOn true phase tau ZI O hphase hZI
  intro r hr z hz
  have hbr := actualTrigModulation_weighted_jet_bound false j r hr O hO phase ZR
    hphase hZR z (hSO hz) tau ell M KR htau htaul hell1 hKR
    (fun a ha => hpb a ha z hz) (fun a ha => hRb a ha z hz)
  have hbi := actualTrigModulation_weighted_jet_bound true j r hr O hO phase ZI
    hphase hZI z (hSO hz) tau ell M KI htau htaul hell1 hKI
    (fun a ha => hpb a ha z hz) (fun a ha => hIb a ha z hz)
  change tau ^ r * ‖iteratedFDeriv ℝ r
    (fun w => actualTrigModulation false phase tau ZR w -
      actualTrigModulation true phase tau ZI w) z‖ ≤ _
  rw [fun_iteratedFDeriv_sub_apply
    ((hR.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))
    ((hI.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp))]
  calc
    _ ≤ tau ^ r * (‖iteratedFDeriv ℝ r (actualTrigModulation false phase tau ZR) z‖ +
        ‖iteratedFDeriv ℝ r (actualTrigModulation true phase tau ZI) z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg htau.le _)
    _ = tau ^ r * ‖iteratedFDeriv ℝ r (actualTrigModulation false phase tau ZR) z‖ +
        tau ^ r * ‖iteratedFDeriv ℝ r (actualTrigModulation true phase tau ZI) z‖ := by ring
    _ ≤ _ := by nlinarith [hbr, hbi]

/-- The actual native `Du Dxx` response follows from total third jets. The
bound intentionally retains the extra inverse tau, which the exact original
scale absorption below pays for without changing the final probe allowance. -/
theorem actual_secondary_native_hessian_response_of_total_jets
    (W : Ep × Es → EuclideanSpace ℝ (Fin N))
    (O S : Set (Ep × Es)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hW : ContDiffOn ℝ ∞ W O)
    (tau delta C : ℝ) (htau : 0 < tau)
    (hWb : ∀ z ∈ S, tau ^ 3 * ‖iteratedFDeriv ℝ 3 W z‖ ≤ C * delta ^ 2) :
    ∀ z ∈ S, ‖fderiv ℝ
      (fun p => fderiv ℝ (fderiv ℝ (fun x => W (p, x))) z.2) z.1‖ ≤
        C * delta ^ 2 / tau ^ 3 := by
  intro z hz
  exact (actual_parameter_spatial_hessian_norm_le hO hW (hSO hz)).trans
    ((le_div_iff₀ (pow_pos htau 3)).2 (by simpa only [mul_comm] using hWb z hz))

/-- Original-scale native Hessian response for every stage `k >= 10`.
The same actual function W occurs in the native derivative and total budget. -/
theorem actual_secondary_native_hessian_original_scale
    (W : Ep × Es → EuclideanSpace ℝ (Fin N))
    (O S : Set (Ep × Es)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hW : ContDiffOn ℝ ∞ W O)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k : ℕ) (hk : 10 ≤ k)
    (C : ℝ) (hC : 0 ≤ C)
    (hWb : ∀ z ∈ S, (t ^ (6 / 5 : ℝ)) ^ 3 * ‖iteratedFDeriv ℝ 3 W z‖ ≤ C * (t ^ k) ^ 2) :
    ∀ z ∈ S, ‖fderiv ℝ
      (fun p => fderiv ℝ (fderiv ℝ (fun x => W (p, x))) z.2) z.1‖ ≤
        C * (t ^ k / t ^ (6 / 5 : ℝ)) *
          (t ^ (6 / 5 : ℝ) / t ^ (11 / 10 : ℝ)) := by
  intro z hz
  exact (actual_secondary_native_hessian_response_of_total_jets W O S hO hSO hW
    (t ^ (6 / 5 : ℝ)) (t ^ k) C (Real.rpow_pos_of_pos ht _) hWb z hz).trans
    (secondary_original_scale_hessian_response ht ht1 k hk C hC)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualSecondaryModulation_weighted_jets
#print axioms GlobalEmbedding.Continuation.actual_secondary_native_hessian_response_of_total_jets
#print axioms GlobalEmbedding.Continuation.actual_secondary_native_hessian_original_scale
