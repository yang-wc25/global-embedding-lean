import Smoothing.WeightedCoerciveInverse
import GlobalEmbedding.Paper.IncrementsWeightedFirstOrder
import GlobalEmbedding.Paper.FreeGramRightInverse
import GlobalEmbedding.Paper.NormalProjectionGramFormula

/-!
# Uniform slow jets of the actual Gram inverse and reconstruction

The sole field is the actual frame A. Its singular-value reserve supplies
coercivity of A* A; the native weighted product estimate supplies the Gram
jets; the actual inverse theorem supplies its inverse jets. The published
freeGramRightInverse is then the same A(A* A)^(-1), with quantitative bounds.
The source D may already be a nonzero-dimensional parameter/source product.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation

section Bilinear
variable {D X Y Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The published scaled Leibniz estimate applies to a fixed bounded bilinear
operation. This is a bound on native derivatives of its actual application. -/
theorem slow_bilinear_jet_bound (L : X →L[ℝ] Y →L[ℝ] Z) (hL : ‖L‖ ≤ 1)
    (O : Set D) (hO : IsOpen O) (f : D → X) (g : D → Y)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (j : ℕ) (ell M K : ℝ) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (x : D) (hx : x ∈ O)
    (hfb : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ M)
    (hgb : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k g x‖ ≤ K) :
    ell ^ j * ‖iteratedFDeriv ℝ j (fun y => L (f y) (g y)) x‖ ≤ 2 ^ j * M * K := by
  have hLf : ContDiffOn ℝ ∞ (L ∘ f) O := L.contDiff.comp_contDiffOn hf
  have hLfb : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k (L ∘ f) x‖ ≤ M := by
    intro k hk
    have h := L.norm_iteratedFDeriv_comp_left (hf.contDiffAt (hO.mem_nhds hx)) (n := k) (by simp)
    calc
      _ ≤ ell ^ k * (‖L‖ * ‖iteratedFDeriv ℝ k f x‖) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hell k)
      _ = ‖L‖ * (ell ^ k * ‖iteratedFDeriv ℝ k f x‖) := by ring
      _ ≤ ‖L‖ * M := mul_le_mul_of_nonneg_left (hfb k hk) L.opNorm_nonneg
      _ ≤ M := mul_le_of_le_one_left hM hL
  simpa only [Nat.add_zero, comp_apply] using
    scaled_clm_apply O hO (L ∘ f) g hLf hg j 0 ell M K hell hLfb
      (fun k hk => by simpa using hgb k hk) hx

end Bilinear

section Gram
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Real adjoint is the actual fixed isometry on the operator space. -/
theorem actual_adjoint_slow_jets (A : D → E →L[ℝ] F)
    (j : ℕ) (ell M : ℝ) (O : Set D)
    (hjet : ∀ k ≤ j, ∀ x ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y => (A y).adjoint) x‖ ≤ M := by
  let e : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E) := ContinuousLinearMap.adjoint
  intro k hk x hx
  have he := e.norm_iteratedFDeriv_comp_left A x k
  change ‖iteratedFDeriv ℝ k (fun y => (A y).adjoint) x‖ = _ at he
  rw [he]
  exact hjet k hk x hx

/-- Genuine Gram fields have slow jets controlled by the actual frame jets. -/
theorem actual_gram_slow_jets (A : D → E →L[ℝ] F) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (j : ℕ) (ell M : ℝ) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (hjet : ∀ k ≤ j, ∀ x ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ContDiffOn ℝ ∞ (fun x => (A x).adjoint.comp (A x)) O ∧
    ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y => (A y).adjoint.comp (A y)) x‖ ≤ 2 ^ j * M ^ 2 := by
  let adj : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
  have hadj : ContDiffOn ℝ ∞ (fun x => (A x).adjoint) O := adj.contDiff.comp_contDiffOn hA
  refine ⟨hadj.clm_comp hA, ?_⟩
  intro k hk x hx
  have hb := actual_adjoint_slow_jets A j ell M O hjet
  have hh := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ E F E)
    (ContinuousLinearMap.norm_compL_le ℝ E F E) O hO (fun x => (A x).adjoint) A
    hadj hA k ell M M hell hM x hx
    (fun r hr => hb r (hr.trans hk) x hx) (fun r hr => hjet r (hr.trans hk) x hx)
  apply hh.trans
  have hp : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hk
  nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg M)]

/-- The actual frame reserve supplies the actual Gram coercivity inequality. -/
theorem actual_gram_coercive (A : E →L[ℝ] F) (c : ℝ)
    (hreserve : ∀ v : E, c * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2) (v : E) :
    c * ‖v‖ ^ 2 ≤ inner ℝ v ((A.adjoint.comp A) v) := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq] using hreserve v

/-- Uniform all-order slow bounds for the SAME actual Gram inverse. -/
theorem actual_gram_inverse_slow_jets (A : D → E →L[ℝ] F) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (j : ℕ) (ell c M : ℝ)
    (hell : 0 < ell) (hc : 0 < c) (hM : 0 ≤ M)
    (hreserve : ∀ x ∈ O, ∀ v : E, c * ‖v‖ ^ 2 ≤ ‖A x v‖ ^ 2)
    (hjet : ∀ k ≤ j, ∀ x ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ContDiffOn ℝ ∞ (fun x => ((A x).adjoint.comp (A x)).inverse) O ∧
    ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y => ((A y).adjoint.comp (A y)).inverse) x‖ ≤
        slowInverseMajorant c⁻¹ (2 ^ j * M ^ 2) j := by
  obtain ⟨hG, hGb⟩ := actual_gram_slow_jets A O hO hA j ell M hell.le hM hjet
  have h := actual_coercive_inverse_slow_jets j O hO
    (fun x => (A x).adjoint.comp (A x)) hG c ell (2 ^ j * M ^ 2) hc hell (by positivity)
    (fun x hx => actual_gram_coercive (A x) c (hreserve x hx))
    (fun k _ hk x hx => hGb k hk x hx)
  exact h.2

/-- The actual published tangent/normal reconstruction inverse has slow jets
from its actual frame and its fixed reserve, with no supplied output bound. -/
theorem actual_freeGramRightInverse_slow_jets
    (A : D → E →L[ℝ] F) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (j : ℕ) (ell c M : ℝ)
    (hell : 0 < ell) (hc : 0 < c) (hM : 0 ≤ M)
    (hreserve : ∀ x ∈ O, ∀ v : E, c * ‖v‖ ^ 2 ≤ ‖A x v‖ ^ 2)
    (hjet : ∀ k ≤ j, ∀ x ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ContDiffOn ℝ ∞ (fun x => freeGramRightInverse (A x)) O ∧
    ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y => freeGramRightInverse (A y)) x‖ ≤
        2 ^ j * M * slowInverseMajorant c⁻¹ (2 ^ j * M ^ 2) j := by
  obtain ⟨hI, hIb⟩ := actual_gram_inverse_slow_jets A O hO hA j ell c M hell hc hM hreserve hjet
  refine ⟨hA.clm_comp hI, ?_⟩
  intro k hk x hx
  have hh := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ E E F)
    (ContinuousLinearMap.norm_compL_le ℝ E E F) O hO A
    (fun y => ((A y).adjoint.comp (A y)).inverse) hA hI k ell M
    (slowInverseMajorant c⁻¹ (2 ^ j * M ^ 2) j) hell.le hM x hx
    (fun r hr => hjet r (hr.trans hk) x hx) (fun r hr => hIb r (hr.trans hk) x hx)
  apply hh.trans
  have hR : 0 ≤ slowInverseMajorant c⁻¹ (2 ^ j * M ^ 2) j :=
    slowInverseMajorant_nonneg (inv_nonneg.mpr hc.le) (by positivity) j
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hM) hR

end Gram

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_gram_inverse_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_freeGramRightInverse_slow_jets
