import Probes.ActualIncrementSampleInverse
import Smoothing.WeightedActualProjection

/-! Actual Gram inverses on the true open domain, with reserves and joint-jet
budgets only on the original samples. Qualitative injectivity on the open
domain supplies smoothness; sampled coercivity supplies the inverse norm.
The original majorants and actual freeGramRightInverse are unchanged. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem actual_gram_inverse_slow_jets_on_samples
    (A : D → E →L[ℝ] F) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ A O) (hinj : ∀ x ∈ O, Function.Injective (A x))
    (j : ℕ) (ell c M : ℝ) (hell : 0 < ell) (hc : 0 < c) (hM : 0 ≤ M)
    (hreserve : ∀ x ∈ S, ∀ v : E, c*‖v‖^2 ≤ ‖A x v‖^2)
    (hjet : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ContDiffOn ℝ ∞ (fun x => ((A x).adjoint.comp (A x)).inverse) O ∧
      ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y => ((A y).adjoint.comp (A y)).inverse) x‖ ≤
          slowInverseMajorant c⁻¹ (2^j*M^2) j := by
  let adj : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
  let G := fun x => (A x).adjoint.comp (A x)
  have hadj : ContDiffOn ℝ ∞ (fun x => (A x).adjoint) O := adj.contDiff.comp_contDiffOn hA
  have hG : ContDiffOn ℝ ∞ G O := hadj.clm_comp hA
  have hGinv : ∀ x ∈ O, (G x).IsInvertible :=
    fun x hx => (frame_gram_positive_invertible (A x) (hinj x hx)).2.2
  have hI : ContDiffOn ℝ ∞ (fun x => (G x).inverse) O := by
    intro x hx
    exact (((hGinv x hx).contDiffAt_map_inverse).comp x
      (hG.contDiffAt (hO.mem_nhds hx))).contDiffWithinAt
  have hunit : ∀ x ∈ O, IsUnit (G x) :=
    fun x hx => (G x).isUnit_iff_bijective.mpr (hGinv x hx).bijective
  have hval : ∀ x ∈ S, ‖Ring.inverse (G x)‖ ≤ c⁻¹ := by
    intro x hx
    have hh := (coercive_inverse_smooth_bound univ isOpen_univ
      (fun _ : ℝ => G x) c hc contDiffOn_const
      (fun _ _ => actual_gram_coercive (A x) c (hreserve x hx))).1 0 (mem_univ 0)
    simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using hh.2
  have hadjb := actual_adjoint_slow_jets A j ell M S hjet
  have hGb : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k G x‖ ≤ 2^j*M^2 := by
    intro k hk x hx
    have hh := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ E F E)
      (ContinuousLinearMap.norm_compL_le ℝ E F E) O hO (fun x => (A x).adjoint) A
      hadj hA k ell M M hell.le hM x (hSO hx)
      (fun r hr => hadjb r (hr.trans hk) x hx) (fun r hr => hjet r (hr.trans hk) x hx)
    apply hh.trans
    have hp : (2 : ℝ)^k ≤ 2^j := pow_le_pow_right₀ (by norm_num) hk
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg M)]
  have hb := actual_inverse_slow_weighted_jets_on_samples j O S hO hSO G hG hunit ell c⁻¹
    (2^j*M^2) hell (inv_nonneg.mpr hc.le) (by positivity) hval
    (fun k _ hk x hx => hGb k hk x hx)
  refine ⟨hI,?_⟩
  simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using hb j le_rfl

theorem actual_freeGramRightInverse_slow_jets_on_samples
    (A : D → E →L[ℝ] F) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ A O) (hinj : ∀ x ∈ O, Function.Injective (A x))
    (j : ℕ) (ell c M : ℝ) (hell : 0 < ell) (hc : 0 < c) (hM : 0 ≤ M)
    (hreserve : ∀ x ∈ S, ∀ v : E, c*‖v‖^2 ≤ ‖A x v‖^2)
    (hjet : ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ContDiffOn ℝ ∞ (fun x => freeGramRightInverse (A x)) O ∧
      ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y => freeGramRightInverse (A y)) x‖ ≤
          2^j*M*slowInverseMajorant c⁻¹ (2^j*M^2) j := by
  obtain ⟨hI,hIb⟩ := actual_gram_inverse_slow_jets_on_samples A O S hO hSO hA hinj j ell c M
    hell hc hM hreserve hjet
  refine ⟨hA.clm_comp hI,?_⟩
  intro k hk x hx
  have hh := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ E E F)
    (ContinuousLinearMap.norm_compL_le ℝ E E F) O hO A
    (fun y => ((A y).adjoint.comp (A y)).inverse) hA hI k ell M
    (slowInverseMajorant c⁻¹ (2^j*M^2) j) hell.le hM x (hSO hx)
    (fun r hr => hjet r (hr.trans hk) x hx) (fun r hr => hIb r (hr.trans hk) x hx)
  apply hh.trans
  have hR : 0 ≤ slowInverseMajorant c⁻¹ (2^j*M^2) j :=
    slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le) (by positivity) j
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hM) hR

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_gram_inverse_slow_jets_on_samples
#print axioms GlobalEmbedding.Continuation.actual_freeGramRightInverse_slow_jets_on_samples
