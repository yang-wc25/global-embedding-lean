import GlobalEmbedding.Paper.IncrementsWeightedFirstOrder

/-!
# Finite iteration of the actual first-order differential expression

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines617–635.
These are actual function iterates, without a bounded endomorphism on Cj and
without asserting totalized differentiation linear on arbitrary raw functions.
The existing actual smooth-section linear realization remains a separate caller.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Every actual iteration costs one slow derivative. The single fixed expression
is iterated before choosing the observation order. Native first-order loss is reused
at each step; no operator-loss estimate is assumed. Coefficient and initial source
bounds are honest scaled jets. This includes p=0 and empty/zero-dimensional domains.
Source: `lem:increments`, lines617–635. -/
theorem increments_first_order_scaled_iterate
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E) (f : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hf : ContDiffOn ℝ ∞ f O)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
    (hfb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ K) :
    let L : (D → E) → D → E := fun u x ↦ B x (u x) + A x (fderiv ℝ u x)
    ∀ k, k + p ≤ N → ∀ x ∈ S,
      ell ^ (k + p) * ‖iteratedFDeriv ℝ k (L^[p] f) x‖ ≤ (2 * 2 ^ N * M) ^ p * K := by
  let L : (D → E) → D → E := fun u x ↦ B x (u x) + A x (fderiv ℝ u x)
  let C := 2 * 2 ^ N * M
  change ∀ k, k + p ≤ N → ∀ x ∈ S,
    ell ^ (k + p) * ‖iteratedFDeriv ℝ k (L^[p] f) x‖ ≤ C ^ p * K
  have hLs : ∀ t, ContDiffOn ℝ ∞ (L^[t] f) O := by
    intro t
    induction t with
    | zero => simpa using hf
    | succ t ht =>
      rw [Function.iterate_succ_apply']
      exact (hB.clm_apply ht).add
        (hA.clm_apply (ht.fderiv_of_isOpen hO (by simp)))
  induction p with
  | zero =>
    intro k hk x hx
    simpa using hfb k (by simpa using hk) x hx
  | succ p ih =>
    intro k hk x hx
    have hsrc : ∀ i ≤ k + 1, ∀ y ∈ S,
        ell ^ i * ‖iteratedFDeriv ℝ i (L^[p] f) y‖ ≤ (C ^ p * K) / ell ^ p := by
      intro i hi y hy
      apply (le_div_iff₀ (pow_pos hell p)).2
      calc
        _ = ell ^ (i + p) * ‖iteratedFDeriv ℝ i (L^[p] f) y‖ := by
          rw [pow_add]
          ring
        _ ≤ C ^ p * K := ih i (by omega) y hy
    have hs := increments_first_order_scaled_jet k O S hO hSO A B (L^[p] f)
      hA hB (hLs p) ell M ((C ^ p * K) / ell ^ p) hell hell1
      (fun i hi y hy ↦ hAb i (by omega) y hy)
      (fun i hi y hy ↦ hBb i (by omega) y hy) hsrc
    have hbase : 2 * 2 ^ k * M ≤ C := by
      dsimp [C]
      gcongr <;> norm_num
      omega
    calc
      _ = ell ^ p * (ell ^ (k + 1) *
          ‖iteratedFDeriv ℝ k (fun y ↦ B y ((L^[p] f) y) +
            A y (fderiv ℝ (L^[p] f) y)) x‖) := by
        rw [Function.iterate_succ_apply']
        rw [show k + (p + 1) = p + (k + 1) by omega, pow_add]
        ring
      _ ≤ ell ^ p * (2 * 2 ^ k * M * ((C ^ p * K) / ell ^ p)) :=
        mul_le_mul_of_nonneg_left (hs k le_rfl x hx) (by positivity)
      _ = (2 * 2 ^ k * M) * (C ^ p * K) := by field_simp
      _ ≤ C * (C ^ p * K) := mul_le_mul_of_nonneg_right hbase (by dsimp [C]; positivity)
      _ = C ^ (p + 1) * K := by rw [pow_succ]; ring

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.increments_first_order_scaled_iterate
