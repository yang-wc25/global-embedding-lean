import GlobalEmbedding.Paper.FiniteCjNormSpecification
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual local first-order weighted derivative loss

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines617–635.
The coefficient fields and the first derivative below are actual functions. This is
an estimate for their local differential expression, not a bounded operator on Cj.
The differentiation domain O is open; the norm domain S may be any subset of O.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

theorem scaled_clm_apply
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O : Set D) (hO : IsOpen O) (A : D → E →L[ℝ] F) (f : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hf : ContDiffOn ℝ ∞ f O)
    (k s : ℕ) (ell M K : ℝ) (hell : 0 ≤ ell) {x : D}
    (hAb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hfb : ∀ i ≤ k, ell ^ (i + s) * ‖iteratedFDeriv ℝ i f x‖ ≤ K)
    (hx : x ∈ O) :
    ell ^ (k + s) * ‖iteratedFDeriv ℝ k (fun y ↦ A y (f y)) x‖ ≤
      2 ^ k * M * K := by
  have he := norm_iteratedFDerivWithin_clm_apply hA hf hO.uniqueDiffOn hx
    (n := k) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO hx] at he
  calc
    _ ≤ ell ^ (k + s) * ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i A x‖ *
          ‖iteratedFDeriv ℝ (k - i) f x‖ := mul_le_mul_of_nonneg_left he (by positivity)
    _ = ∑ i ∈ Finset.range (k + 1), ell ^ (k + s) *
        ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i A x‖ *
          ‖iteratedFDeriv ℝ (k - i) f x‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M * K := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using hi
      have hp : ell ^ (k + s) = ell ^ i * ell ^ (k - i + s) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      calc
        _ = (k.choose i : ℝ) * (ell ^ i * ‖iteratedFDeriv ℝ i A x‖) *
            (ell ^ (k - i + s) * ‖iteratedFDeriv ℝ (k - i) f x‖) := by ring
        _ ≤ (k.choose i : ℝ) * M * K := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hAb i hik) (by positivity)
          · exact hfb (k - i) (Nat.sub_le _ _)
          · positivity
          · exact mul_nonneg (by positivity)
              ((by positivity : 0 ≤ ell ^ i * ‖iteratedFDeriv ℝ i A x‖).trans (hAb i hik))
    _ = 2 ^ k * M * K := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k

/-- Actual local first-order loss at each jet. Coefficient and source bounds are
honest scaled derivative bounds, not a supplied operator estimate. The same proof
covers zero-dimensional spaces and empty norm domains. Native bilinear derivative
bounds and the isometric derivative-jet shift give one factor ell inverse.
Source: `lem:increments`, lines617–635. -/
theorem increments_first_order_scaled_jet
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] F) (B : D → E →L[ℝ] F) (f : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hf : ContDiffOn ℝ ∞ f O)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hAb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hBb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
    (hfb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ K) :
    ∀ k ≤ j, ∀ x ∈ S,
      ell ^ (k + 1) *
          ‖iteratedFDeriv ℝ k (fun y ↦ B y (f y) + A y (fderiv ℝ f y)) x‖ ≤
        2 * 2 ^ k * M * K := by
  intro k hk x hx
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) O := hf.fderiv_of_isOpen hO (by simp)
  have h0 := scaled_clm_apply O hO B f hB hf k 0 ell M K hell.le
    (fun i hi ↦ hBb i (hi.trans hk) x hx)
    (fun i hi ↦ by simpa using hfb i (by omega) x hx) (hSO hx)
  have h1 := scaled_clm_apply O hO A (fderiv ℝ f) hA hdf k 1 ell M K hell.le
    (fun i hi ↦ hAb i (hi.trans hk) x hx)
    (fun i hi ↦ by rw [norm_iteratedFDeriv_fderiv]; exact hfb (i + 1) (by omega) x hx)
    (hSO hx)
  have h0' : ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun y ↦ B y (f y)) x‖ ≤
      2 ^ k * M * K := by
    apply le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hell.le hell1 (by omega : k ≤ k + 1)) (norm_nonneg _))
    simpa using h0
  have hsum := fun_iteratedFDerivWithin_add_apply (𝕜 := ℝ) (i := k)
    (((hB.clm_apply hf).of_le (by simp)).contDiffWithinAt (hSO hx))
    (((hA.clm_apply hdf).of_le (by simp)).contDiffWithinAt (hSO hx))
    hO.uniqueDiffOn (hSO hx)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO (hSO hx)] at hsum
  rw [hsum]
  calc
    _ ≤ ell ^ (k + 1) *
        (‖iteratedFDeriv ℝ k (fun y ↦ B y (f y)) x‖ +
          ‖iteratedFDeriv ℝ k (fun y ↦ A y (fderiv ℝ f y)) x‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ 2 * 2 ^ k * M * K := by nlinarith [h0', h1]

theorem scaled_finiteCj_points
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (f : D → E) (S : Set D) (ell : ℝ) (hell : 0 ≤ ell)
    (hfinite : ∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖)) :
    0 ≤ (∑ a ∈ Finset.range (j + 1), ell ^ a * finiteCjNorm a f S) ∧
      ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤
        ∑ a ∈ Finset.range (j + 1), ell ^ a * finiteCjNorm a f S := by
  have hn : ∀ a ≤ j, 0 ≤ ell ^ a * finiteCjNorm a f S := by
    intro a ha
    exact mul_nonneg (by positivity)
      (finiteCjNorm_specification a f S (fun k hk ↦ hfinite k (hk.trans ha))).1
  refine ⟨Finset.sum_nonneg (fun a ha ↦ hn a (by simpa using ha)), ?_⟩
  intro k hk x hx
  apply le_trans (mul_le_mul_of_nonneg_left
    ((finiteCjNorm_specification k f S (fun a ha ↦ hfinite a (ha.trans hk))).2.1
      k le_rfl x hx) (by positivity))
  exact Finset.single_le_sum (fun a ha ↦ hn a (by simpa using ha)) (by simpa using hk)

theorem scaled_finiteCj_sum_le
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (f : D → E) (S : Set D) (ell T : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (hT : 0 ≤ T)
    (hf : ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ T) :
    (∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖)) ∧
      (∑ a ∈ Finset.range (j + 1), ell ^ a * finiteCjNorm a f S) ≤
        (∑ a ∈ Finset.range (j + 1), ((a + 1 : ℕ) : ℝ)) * T := by
  have hbound : ∀ a ≤ j, ∀ k ≤ a, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ k f x‖ ≤ T / ell ^ a := by
    intro a ha k hk x hx
    apply (le_div_iff₀ (pow_pos hell a)).2
    calc
      _ ≤ ell ^ k * ‖iteratedFDeriv ℝ k f x‖ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hell.le hell1 hk)
          (norm_nonneg _)
      _ ≤ T := hf k (hk.trans ha) x hx
  have hbdd : ∀ a ≤ j, ∀ k ≤ a,
      BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖) := by
    intro a ha k hk
    exact ⟨T / ell ^ a, by rintro _ ⟨x, rfl⟩; exact hbound a ha k hk x x.property⟩
  refine ⟨fun k hk ↦ hbdd k hk k le_rfl, ?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  have haj : a ≤ j := by simpa using ha
  have hc := (finiteCjNorm_specification a f S (hbdd a haj)).2.2.1
    (fun _ ↦ T / ell ^ a) (fun _ _ ↦ by positivity) (hbound a haj)
  have hc' : finiteCjNorm a f S ≤ ((a + 1 : ℕ) : ℝ) * (T / ell ^ a) := by
    simpa using hc
  calc
    _ ≤ ell ^ a * (((a + 1 : ℕ) : ℝ) * (T / ell ^ a)) :=
      mul_le_mul_of_nonneg_left hc' (by positivity)
    _ = ((a + 1 : ℕ) : ℝ) * T := by
      field_simp

/-- The actual weighted finite-Cj first-order estimate, with actual coefficient
norms and the actual source norm. All real conditional suprema carry honest
boundedness hypotheses. The conclusion also derives the output boundedness.
The coefficient/source norm convention is the literal sum ell^a finiteCjNorm a;
the paper's scalar-partial/atlas comparison is a separate accepted norm provider.
No bounded endomorphism Cj→Cj or desired operator loss is assumed.
Source: `lem:increments`, lines617–635. -/
theorem increments_first_order_weighted_finiteCj
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] F) (B : D → E →L[ℝ] F) (f : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hf : ContDiffOn ℝ ∞ f O)
    (ell M : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hAf : ∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k A x‖))
    (hBf : ∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k B x‖))
    (hff : ∀ k ≤ j + 1, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖))
    (hAM : (∑ a ∈ Finset.range (j + 1), ell ^ a * finiteCjNorm a A S) ≤ M)
    (hBM : (∑ a ∈ Finset.range (j + 1), ell ^ a * finiteCjNorm a B S) ≤ M) :
    (∀ k ≤ j, BddAbove (Set.range fun x : S ↦
      ‖iteratedFDeriv ℝ k (fun y ↦ B y (f y) + A y (fderiv ℝ f y)) x‖)) ∧
    (∑ a ∈ Finset.range (j + 1), ell ^ a *
        finiteCjNorm a (fun y ↦ B y (f y) + A y (fderiv ℝ f y)) S) ≤
      (2 * (∑ a ∈ Finset.range (j + 1), ((a + 1 : ℕ) : ℝ)) * 2 ^ j) * M * ell⁻¹ *
        (∑ a ∈ Finset.range (j + 2), ell ^ a * finiteCjNorm a f S) := by
  let K := ∑ a ∈ Finset.range (j + 2), ell ^ a * finiteCjNorm a f S
  have hAp := scaled_finiteCj_points j A S ell hell.le hAf
  have hBp := scaled_finiteCj_points j B S ell hell.le hBf
  have hfp := scaled_finiteCj_points (j + 1) f S ell hell.le hff
  have hK : 0 ≤ K := by simpa [K, Nat.add_assoc] using hfp.1
  have hM : 0 ≤ M := hAp.1.trans hAM
  have hp := increments_first_order_scaled_jet j O S hO hSO A B f hA hB hf
    ell M K hell hell1
    (fun i hi x hx ↦ (hAp.2 i hi x hx).trans hAM)
    (fun i hi x hx ↦ (hBp.2 i hi x hx).trans hBM)
    (fun i hi x hx ↦ by simpa [K, Nat.add_assoc] using hfp.2 i hi x hx)
  have hpoint : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k *
          ‖iteratedFDeriv ℝ k (fun y ↦ B y (f y) + A y (fderiv ℝ f y)) x‖ ≤
        (2 * 2 ^ j * M * K) / ell := by
    intro k hk x hx
    apply (le_div_iff₀ hell).2
    calc
      _ = ell ^ (k + 1) *
          ‖iteratedFDeriv ℝ k (fun y ↦ B y (f y) + A y (fderiv ℝ f y)) x‖ := by
        rw [pow_succ]
        ring
      _ ≤ 2 * 2 ^ k * M * K := hp k hk x hx
      _ ≤ 2 * 2 ^ j * M * K := by
        gcongr
        norm_num
  have he := scaled_finiteCj_sum_le j
    (fun y ↦ B y (f y) + A y (fderiv ℝ f y)) S ell ((2 * 2 ^ j * M * K) / ell)
    hell hell1 (by positivity) hpoint
  refine ⟨he.1, he.2.trans_eq ?_⟩
  dsimp [K]
  simp only [div_eq_mul_inv]
  ring

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.increments_first_order_scaled_jet
#print axioms GlobalEmbedding.Paper.increments_first_order_weighted_finiteCj

#print axioms GlobalEmbedding.Paper.scaled_finiteCj_sum_le

#print axioms GlobalEmbedding.Paper.scaled_clm_apply
#print axioms GlobalEmbedding.Paper.scaled_finiteCj_points
