import GlobalEmbedding.Paper.IncrementsMeanQuadraticCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Quantitative remainder of the SAME finite primary mean coefficient

Source: original `lem:increments`, main.tex645–661. Exclusive W1.
This packages the existing actual coefficient as a bounded REAL-bilinear map,
then reuses native Leibniz. No spatial averaging, Hermitian replacement, new norm
or section carrier is introduced. The actual reconstructed amplitude bounds are
separate original callers, never additional hypotheses of the full increments target.
-/

noncomputable section
open scoped ComplexConjugate ContDiff
namespace GlobalEmbedding.Paper

variable {Λ I : Type*} [Fintype Λ] [Fintype I] {N : ℕ}

/-- Actual real-bilinear polarization of the existing opposite-primary coefficient.
Coordinate multiplication is complex-bilinear; each conjugation is explicitly real-linear.
Source: exact two orderings and original quarter in main.tex645–661. -/
def incrementsMeanBilinear (i j : I) :
    (Λ → I → Fin N → ℂ) →L[ℝ] (Λ → I → Fin N → ℂ) →L[ℝ] ℂ :=
  let ev (ν : Λ) (a : I) (c : Fin N) : (Λ → I → Fin N → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj c : (Fin N → ℂ) →L[ℝ] ℂ).comp
      ((ContinuousLinearMap.proj a : (I → Fin N → ℂ) →L[ℝ] (Fin N → ℂ)).comp
        (ContinuousLinearMap.proj ν))
  ∑ ν : Λ, (1 / 4 : ℂ) •
    ((∑ c : Fin N, (ContinuousLinearMap.mul ℝ ℂ).bilinearComp
        (ev ν i c) (Complex.conjCLE.toContinuousLinearMap.comp (ev ν j c))) +
      ∑ c : Fin N, (ContinuousLinearMap.mul ℝ ℂ).bilinearComp
        (Complex.conjCLE.toContinuousLinearMap.comp (ev ν i c)) (ev ν j c))

/-- The diagonal is literally the canonical selected contribution, not a new mean.
Source: same finite original coefficient in main.tex645–661. -/
theorem incrementsMeanBilinear_diagonal (D : Λ → I → Fin N → ℂ) (i j : I) :
    incrementsMeanBilinear i j D D = incrementsOppositePrimaryContribution D i j := by
  classical
  simp [incrementsMeanBilinear, incrementsOppositePrimaryContribution, dotProduct,
    smul_eq_mul, mul_add]

/-- The ACTUAL difference from the leading coefficient; no smallness is built in.
Source: original normalized mean error after D=delta*(l+e). -/
def incrementsMeanRemainder (L E : Λ → I → Fin N → ℂ) (i j : I) : ℂ :=
  incrementsOppositePrimaryContribution (L + E) i j -
    incrementsOppositePrimaryContribution L i j

/-- Every actual remainder term contains an error coefficient.
Source: the three polarized pairs are exactly the original six scalar terms. -/
theorem incrementsMeanRemainder_eq (L E : Λ → I → Fin N → ℂ) (i j : I) :
    incrementsMeanRemainder L E i j =
      incrementsMeanBilinear i j L E + incrementsMeanBilinear i j E L +
        incrementsMeanBilinear i j E E := by
  unfold incrementsMeanRemainder
  rw [← incrementsMeanBilinear_diagonal, ← incrementsMeanBilinear_diagonal]
  simp only [map_add, add_apply]
  abel

/-- Native bilinear Leibniz with the SAME slow weights, specialized to the actual
finite mean contraction. The bound is on coefficient jets, not a desired mean estimate.
Source: finite-product estimate used in original (6.3). -/
theorem incrementsMeanBilinear_scaled_jet
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (O : Set D) (hO : IsOpen O) (L E : D → Λ → I → Fin N → ℂ)
    (hL : ContDiffOn ℝ ∞ L O) (hE : ContDiffOn ℝ ∞ E O)
    (i j : I) (k : ℕ) (ell K M : ℝ) (hell : 0 ≤ ell) (hK : 0 ≤ K)
    {x : D} (hx : x ∈ O)
    (hLb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r L x‖ ≤ K)
    (hEb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r E x‖ ≤ M) :
    ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ incrementsMeanBilinear i j (L y) (E y)) x‖ ≤
      ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ * 2 ^ k * K * M := by
  have he := ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear
    (incrementsMeanBilinear (Λ := Λ) (N := N) i j) hL hE hO.uniqueDiffOn hx
      (n := k) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO hx] at he
  calc
    _ ≤ ell ^ k * (‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ *
        ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) *
          ‖iteratedFDeriv ℝ r L x‖ * ‖iteratedFDeriv ℝ (k - r) E x‖) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hell k)
    _ = ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ *
        ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) *
          (ell ^ r * ‖iteratedFDeriv ℝ r L x‖) *
          (ell ^ (k - r) * ‖iteratedFDeriv ℝ (k - r) E x‖) := by
      rw [mul_left_comm, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      have hrk : r ≤ k := by simpa using hr
      have hp : ell ^ k = ell ^ r * ell ^ (k - r) := by
        rw [← pow_add, Nat.add_sub_of_le hrk]
      rw [hp]
      ring
    _ ≤ ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ *
        ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) * K * M := by
      refine mul_le_mul_of_nonneg_left ?_
        (norm_nonneg (incrementsMeanBilinear (Λ := Λ) (N := N) i j))
      apply Finset.sum_le_sum
      intro r hr
      have hrk : r ≤ k := by simpa using hr
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hLb r hrk) (by positivity))
        (hEb (k - r) (Nat.sub_le _ _)) (by positivity) (mul_nonneg (by positivity) hK)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hc : (∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ)) = 2 ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [hc]
      ring


/-- The actual mean remainder retains the error's small factor in EVERY slow jet.
The coefficient bounds are actual upstream outputs, not new final-target assumptions.
Source: the size estimate for T in main.tex645–661. -/
theorem incrementsMeanRemainder_scaled_jet
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (O : Set D) (hO : IsOpen O) (L E : D → Λ → I → Fin N → ℂ)
    (hL : ContDiffOn ℝ ∞ L O) (hE : ContDiffOn ℝ ∞ E O)
    (i j : I) (k : ℕ) (ell M epsilon : ℝ) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) {x : D} (hx : x ∈ O)
    (hLb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r L x‖ ≤ M)
    (hEb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r E x‖ ≤ M * epsilon) :
    ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ incrementsMeanRemainder (L y) (E y) i j) x‖ ≤
      3 * ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ * 2 ^ k * M ^ 2 * epsilon := by
  let B := incrementsMeanBilinear (Λ := Λ) (N := N) i j
  let f := fun y ↦ B (L y) (E y)
  let g := fun y ↦ B (E y) (L y)
  let h := fun y ↦ B (E y) (E y)
  have hfs : ContDiffOn ℝ ∞ f O := (B.contDiff.comp_contDiffOn hL).clm_apply hE
  have hgs : ContDiffOn ℝ ∞ g O := (B.contDiff.comp_contDiffOn hE).clm_apply hL
  have hhs : ContDiffOn ℝ ∞ h O := (B.contDiff.comp_contDiffOn hE).clm_apply hE
  have hfg := fun_iteratedFDerivWithin_add_apply (𝕜 := ℝ) (i := k)
    ((hfs.of_le (by simp)).contDiffWithinAt hx)
    ((hgs.of_le (by simp)).contDiffWithinAt hx) hO.uniqueDiffOn hx
  have hfgh := fun_iteratedFDerivWithin_add_apply (𝕜 := ℝ) (i := k)
    (((hfs.add hgs).of_le (by simp)).contDiffWithinAt hx)
    ((hhs.of_le (by simp)).contDiffWithinAt hx) hO.uniqueDiffOn hx
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO hx] at hfg hfgh
  have hr : (fun y ↦ incrementsMeanRemainder (L y) (E y) i j) =
      fun y ↦ (f y + g y) + h y := by
    funext y
    exact incrementsMeanRemainder_eq (L y) (E y) i j
  rw [hr, hfgh, hfg]
  have hb0 := incrementsMeanBilinear_scaled_jet O hO L E hL hE i j k ell M
    (M * epsilon) hell hM hx hLb hEb
  have hb1 := incrementsMeanBilinear_scaled_jet O hO E L hE hL i j k ell
    (M * epsilon) M hell (mul_nonneg hM hepsilon) hx hEb hLb
  have hb2 := incrementsMeanBilinear_scaled_jet O hO E E hE hE i j k ell
    (M * epsilon) (M * epsilon) hell (mul_nonneg hM hepsilon) hx hEb hEb
  let C := ‖B‖ * 2 ^ k
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg B) (by positivity)
  change ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ C * M * (M * epsilon) at hb0
  change ell ^ k * ‖iteratedFDeriv ℝ k g x‖ ≤ C * (M * epsilon) * M at hb1
  change ell ^ k * ‖iteratedFDeriv ℝ k h x‖ ≤
    C * (M * epsilon) * (M * epsilon) at hb2
  suffices hs : ell ^ k * ‖iteratedFDeriv ℝ k f x + iteratedFDeriv ℝ k g x +
      iteratedFDeriv ℝ k h x‖ ≤ 3 * C * M ^ 2 * epsilon by
    simpa only [C, B, mul_assoc] using hs
  calc
    _ ≤ ell ^ k * (‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k g x‖ +
        ‖iteratedFDeriv ℝ k h x‖) := mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) (by positivity)
    _ ≤ C * M * (M * epsilon) + C * (M * epsilon) * M +
        C * (M * epsilon) * (M * epsilon) := by nlinarith [hb0, hb1, hb2]
    _ ≤ _ := by
      have heps : epsilon ^ 2 ≤ epsilon := by
        nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr hepsilon1)]
      have he := mul_le_mul_of_nonneg_left heps (mul_nonneg hC (sq_nonneg M))
      nlinarith


/-- Exact telescoping between two actual mean remainders. Each product retains
an error or an error difference; the same finite loss is used only once.
Source: original (6.3), not a supplied Lipschitz bound. -/
theorem incrementsMeanRemainder_sub_eq (L E Lbar Ebar : Λ → I → Fin N → ℂ)
    (i j : I) :
    incrementsMeanRemainder L E i j - incrementsMeanRemainder Lbar Ebar i j =
      incrementsMeanBilinear i j (L - Lbar) E +
      incrementsMeanBilinear i j Lbar (E - Ebar) +
      incrementsMeanBilinear i j (E - Ebar) L +
      incrementsMeanBilinear i j Ebar (L - Lbar) +
      incrementsMeanBilinear i j (E - Ebar) E +
      incrementsMeanBilinear i j Ebar (E - Ebar) := by
  rw [incrementsMeanRemainder_eq, incrementsMeanRemainder_eq]
  simp only [map_sub, sub_apply]
  abel

/-- Native finite-sum Leibniz for the ACTUAL fixed mean contraction.
This is the finite sum used by its six-term difference, not a new norm framework.
Source: finite coefficient products in original (6.3). -/
theorem incrementsMeanBilinear_scaled_sum
    {D A : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype A]
    (O : Set D) (hO : IsOpen O) (F G : A → D → Λ → I → Fin N → ℂ)
    (hF : ∀ a, ContDiffOn ℝ ∞ (F a) O) (hG : ∀ a, ContDiffOn ℝ ∞ (G a) O)
    (i j : I) (k : ℕ) (ell : ℝ) (K M : A → ℝ) (hell : 0 ≤ ell)
    (hK : ∀ a, 0 ≤ K a) {x : D} (hx : x ∈ O)
    (hFb : ∀ a, ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r (F a) x‖ ≤ K a)
    (hGb : ∀ a, ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r (G a) x‖ ≤ M a) :
    ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ ∑ a, incrementsMeanBilinear i j (F a y) (G a y)) x‖ ≤
      ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ * 2 ^ k * ∑ a, K a * M a := by
  let B := incrementsMeanBilinear (Λ := Λ) (N := N) i j
  have hs : ∀ a, ContDiffOn ℝ ∞ (fun y ↦ B (F a y) (G a y)) O :=
    fun a ↦ (B.contDiff.comp_contDiffOn (hF a)).clm_apply (hG a)
  have he := iteratedFDerivWithin_fun_sum_apply (𝕜 := ℝ) (i := k)
    (u := Finset.univ) hO.uniqueDiffOn hx
      (fun a _ ↦ ((hs a).of_le (by simp)).contDiffWithinAt hx)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO hx] at he
  change ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ ∑ a, B (F a y) (G a y)) x‖ ≤ _
  rw [he]
  calc
    _ ≤ ell ^ k * ∑ a, ‖iteratedFDeriv ℝ k (fun y ↦ B (F a y) (G a y)) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hell k)
    _ = ∑ a, ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ B (F a y) (G a y)) x‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ a, ‖B‖ * 2 ^ k * K a * M a := by
      apply Finset.sum_le_sum
      intro a ha
      exact incrementsMeanBilinear_scaled_jet O hO (F a) (G a) (hF a) (hG a)
        i j k ell (K a) (M a) hell (hK a) hx (hFb a) (hGb a)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring


/-- The SAME actual mean remainder difference retains epsilon in every slow jet.
Delta is the actual original input-difference bound at the one fixed loss order;
no loss is applied twice. Actual amplitude bounds must still be derived upstream.
Source: original (6.3). -/
theorem incrementsMeanRemainder_difference_scaled_jet
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (O : Set D) (hO : IsOpen O) (L E Lbar Ebar : D → Λ → I → Fin N → ℂ)
    (hL : ContDiffOn ℝ ∞ L O) (hE : ContDiffOn ℝ ∞ E O)
    (hLbar : ContDiffOn ℝ ∞ Lbar O) (hEbar : ContDiffOn ℝ ∞ Ebar O)
    (i j : I) (k : ℕ) (ell M epsilon Delta : ℝ) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hDelta : 0 ≤ Delta)
    {x : D} (hx : x ∈ O)
    (hLb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r L x‖ ≤ M)
    (hEbarb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r Ebar x‖ ≤ M * epsilon)
    (hLbarb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r Lbar x‖ ≤ M)
    (hEb : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r E x‖ ≤ M * epsilon)
    (hLdiff : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r (L - Lbar) x‖ ≤ M * Delta)
    (hEdiff : ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r (E - Ebar) x‖ ≤
      M * epsilon * Delta) :
    ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ incrementsMeanRemainder (L y) (E y) i j -
        incrementsMeanRemainder (Lbar y) (Ebar y) i j) x‖ ≤
      6 * ‖incrementsMeanBilinear (Λ := Λ) (N := N) i j‖ * 2 ^ k *
        M ^ 2 * epsilon * Delta := by
  let B := incrementsMeanBilinear (Λ := Λ) (N := N) i j
  let F : Fin 6 → D → Λ → I → Fin N → ℂ :=
    ![L - Lbar, Lbar, E - Ebar, Ebar, E - Ebar, Ebar]
  let G : Fin 6 → D → Λ → I → Fin N → ℂ :=
    ![E, E - Ebar, L, L - Lbar, E, E - Ebar]
  let K : Fin 6 → ℝ :=
    ![M * Delta, M, M * epsilon * Delta, M * epsilon, M * epsilon * Delta, M * epsilon]
  let P : Fin 6 → ℝ :=
    ![M * epsilon, M * epsilon * Delta, M, M * Delta, M * epsilon, M * epsilon * Delta]
  have hF : ∀ a, ContDiffOn ℝ ∞ (F a) O := by
    intro a
    fin_cases a
    · exact hL.sub hLbar
    · exact hLbar
    · exact hE.sub hEbar
    · exact hEbar
    · exact hE.sub hEbar
    · exact hEbar
  have hG : ∀ a, ContDiffOn ℝ ∞ (G a) O := by
    intro a
    fin_cases a
    · exact hE
    · exact hE.sub hEbar
    · exact hL
    · exact hL.sub hLbar
    · exact hE
    · exact hE.sub hEbar
  have hK : ∀ a, 0 ≤ K a := by
    intro a
    fin_cases a <;> dsimp [K] <;> positivity
  have hFb : ∀ a, ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r (F a) x‖ ≤ K a := by
    intro a
    fin_cases a
    · exact hLdiff
    · exact hLbarb
    · exact hEdiff
    · exact hEbarb
    · exact hEdiff
    · exact hEbarb
  have hGb : ∀ a, ∀ r ≤ k, ell ^ r * ‖iteratedFDeriv ℝ r (G a) x‖ ≤ P a := by
    intro a
    fin_cases a
    · exact hEb
    · exact hEdiff
    · exact hLb
    · exact hLdiff
    · exact hEb
    · exact hEdiff
  have hr : (fun y ↦ incrementsMeanRemainder (L y) (E y) i j -
        incrementsMeanRemainder (Lbar y) (Ebar y) i j) =
      fun y ↦ ∑ a, B (F a y) (G a y) := by
    funext y
    rw [incrementsMeanRemainder_sub_eq]
    simp [B, F, G, Fin.sum_univ_succ, add_assoc]; abel
  rw [hr]
  have hb := incrementsMeanBilinear_scaled_sum O hO F G hF hG i j k ell K P hell hK hx hFb hGb
  let C := ‖B‖ * 2 ^ k
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg B) (by positivity)
  have hsum : C * ∑ a, K a * P a ≤ 6 * C * M ^ 2 * epsilon * Delta := by
    simp [K, P, Fin.sum_univ_succ]
    have heps : epsilon ^ 2 ≤ epsilon := by
      nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr hepsilon1)]
    have he := mul_le_mul_of_nonneg_left heps
      (mul_nonneg (mul_nonneg hC (sq_nonneg M)) hDelta)
    nlinarith
  have hout := hb.trans hsum
  simpa only [C, B, mul_assoc] using hout


/-- Exact delta homogeneity of the SAME selected coefficient, including delta zero.
Source: normalization of the original actual primary amplitudes, main.tex645–661. -/
theorem incrementsOppositePrimaryContribution_smul
    (delta : ℝ) (D : Λ → I → Fin N → ℂ) (i j : I) :
    incrementsOppositePrimaryContribution (delta • D) i j =
      delta ^ 2 • incrementsOppositePrimaryContribution D i j := by
  rw [← incrementsMeanBilinear_diagonal, ← incrementsMeanBilinear_diagonal]
  simp only [map_smul, smul_apply, smul_smul, pow_two]

/-- Quadratic normalization retains the actual original error formula and its
external delta squared; this asserts no unproved delta-inverse amplitude bound.
Source: the definition of T in original main.tex645–661. -/
theorem incrementsMeanRemainder_smul
    (delta : ℝ) (L E : Λ → I → Fin N → ℂ) (i j : I) :
    incrementsMeanRemainder (delta • L) (delta • E) i j =
      delta ^ 2 • incrementsMeanRemainder L E i j := by
  unfold incrementsMeanRemainder
  rw [← smul_add, incrementsOppositePrimaryContribution_smul,
    incrementsOppositePrimaryContribution_smul, smul_sub]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsMeanBilinear
#print axioms GlobalEmbedding.Paper.incrementsMeanBilinear_diagonal
#print axioms GlobalEmbedding.Paper.incrementsMeanBilinear_scaled_jet
#print axioms GlobalEmbedding.Paper.incrementsMeanBilinear_scaled_sum
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_difference_scaled_jet
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_eq
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_scaled_jet
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_smul
#print axioms GlobalEmbedding.Paper.incrementsMeanRemainder_sub_eq
#print axioms GlobalEmbedding.Paper.incrementsOppositePrimaryContribution_smul
