import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization` proof, smooth inverse dependence, with the explicit inverse
first derivative also written at lines1401 and2518. -/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Dimension-free bounds for all derivatives of an inverse field on an open set.
The numerical majorant depends only on the value inverse bound and the supplied
positive-order derivative bound. The statement accepts any sequence with the
explicit recurrence, so its choice can precede all spaces and fields.

Proof: differentiate F=P⁻¹ as DF=-mulLeftRight(F,F) composed with DP. Two binomial
bilinear estimates, whose operator norms are at most one, bound the next derivative
by 4^k Rk² m. The recurrence absorbs this bound and preserves all lower orders.
Source: `prop:initialization` proof, line822; inverse derivative lines1401 and2518. -/
theorem inverse_derivative_bounds
    {D A : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (j : ℕ) (U : Set D) (hU : IsOpen U) (P : D → A)
    (hP : ContDiffOn ℝ ∞ P U) (hunit : ∀ x ∈ U, IsUnit (P x))
    (b m : ℝ) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hval : ∀ x ∈ U, ‖Ring.inverse (P x)‖ ≤ b)
    (hder : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ U, ‖iteratedFDeriv ℝ k P x‖ ≤ m)
    (R : ℕ → ℝ) (hR0 : R 0 = 1 + b)
    (hRstep : ∀ k, R (k + 1) = R k + 4 ^ k * R k ^ 2 * m) :
    ∀ k ≤ j, ∀ r ≤ k, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ r (fun y ↦ Ring.inverse (P y)) x‖ ≤ R k := by
  let F : D → A := fun y ↦ Ring.inverse (P y)
  have hF : ContDiffOn ℝ ∞ F U := by
    intro x hx
    have hi := contDiffAt_ringInverse ℝ (n := ∞) (hunit x hx).unit
    rw [(hunit x hx).unit_spec] at hi
    exact (hi.comp x (hP.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  have hDF : Set.EqOn (fderivWithin ℝ F U)
      (fun x ↦ -(ContinuousLinearMap.mulLeftRight ℝ A (F x) (F x)).comp
        (fderivWithin ℝ P U x)) U := by
    intro x hx
    have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (hunit x hx).unit
    have hspec : Ring.inverse (P x) = ↑(hunit x hx).unit⁻¹ := by
      exact (congrArg Ring.inverse (hunit x hx).unit_spec).symm.trans
        (Ring.inverse_unit (hunit x hx).unit)
    rw [(hunit x hx).unit_spec, ← hspec] at hi
    have hp := ((hP.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hf := (hi.comp x hp).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffOn x hx)
    simpa only [Function.comp_def, fderivWithin_of_isOpen hU hx,
      ContinuousLinearMap.neg_comp] using hf
  have hRnonneg : ∀ k, 0 ≤ R k := by
    intro k
    induction k with
    | zero => rw [hR0]; positivity
    | succ k hk => rw [hRstep]; positivity
  have hRle : ∀ k, R k ≤ R (k + 1) := by
    intro k
    rw [hRstep]
    exact le_add_of_nonneg_right (by positivity)
  have hchoose : ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    intro k
    exact_mod_cast Nat.sum_range_choose k
  have hFw : ∀ k ≤ j, ∀ r ≤ k, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ r F U x‖ ≤ R k := by
    intro k
    induction k with
    | zero =>
      intro hkj r hr x hx
      have : r = 0 := by omega
      subst r
      rw [norm_iteratedFDerivWithin_zero]
      exact (hval x hx).trans (by rw [hR0]; linarith)
    | succ k hk =>
      intro hkj r hr x hx
      have hkJ : k ≤ j := by omega
      have hRk : 0 ≤ R k := hRnonneg k
      by_cases hrk : r ≤ k
      · exact (hk hkJ r hrk x hx).trans (hRle k)
      have hrEq : r = k + 1 := by omega
      subst r
      let H : D → A →L[ℝ] A :=
        fun y ↦ ContinuousLinearMap.mulLeftRight ℝ A (F y) (F y)
      have hH : ContDiffOn ℝ ∞ H U := by
        exact (contDiffOn_const.clm_apply hF).clm_apply hF
      have hHd : ∀ i ≤ k, ‖iteratedFDerivWithin ℝ i H U x‖ ≤ 2 ^ i * R k ^ 2 := by
        intro i hik
        have he := (ContinuousLinearMap.mulLeftRight ℝ A)
          |>.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hF hF hU.uniqueDiffOn hx
            (n := i) (by simp) (ContinuousLinearMap.opNorm_mulLeftRight_le ℝ A)
        refine he.trans ?_
        calc
          _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * R k * R k := by
            apply Finset.sum_le_sum
            intro l hl
            have hlk : l ≤ k := (by simpa using hl : l ≤ i).trans hik
            gcongr
            · exact hk hkJ l hlk x hx
            · exact hk hkJ (i - l) (by omega) x hx
          _ = 2 ^ i * R k ^ 2 := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
            ring
      have hDP : ContDiffOn ℝ ∞ (fderivWithin ℝ P U) U :=
        hP.fderivWithin hU.uniqueDiffOn (by simp)
      have hnext : ‖iteratedFDerivWithin ℝ (k + 1) F U x‖ ≤
          4 ^ k * R k ^ 2 * m := by
        rw [← norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hx]
        rw [iteratedFDerivWithin_congr hDF hx]
        change ‖iteratedFDerivWithin ℝ k
          (-(fun y ↦ (H y).comp (fderivWithin ℝ P U y))) U x‖ ≤ _
        rw [iteratedFDerivWithin_neg_apply hU.uniqueDiffOn hx, norm_neg]
        have he := (ContinuousLinearMap.compL ℝ D A A)
          |>.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hH hDP hU.uniqueDiffOn hx
            (n := k) (by simp) (ContinuousLinearMap.norm_compL_le ℝ D A A)
        refine he.trans ?_
        calc
          _ ≤ ∑ i ∈ Finset.range (k + 1),
              (k.choose i : ℝ) * (2 ^ k * R k ^ 2) * m := by
            apply Finset.sum_le_sum
            intro i hi
            have hik : i ≤ k := by simpa using hi
            have hHi : ‖iteratedFDerivWithin ℝ i H U x‖ ≤ 2 ^ k * R k ^ 2 :=
              (hHd i hik).trans (mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hik) (sq_nonneg _))
            have hPi : ‖iteratedFDerivWithin ℝ (k - i)
                (fderivWithin ℝ P U) U x‖ ≤ m := by
              rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hx,
                iteratedFDerivWithin_of_isOpen _ hU hx]
              exact hder _ (by omega) (by omega) x hx
            gcongr
          _ = 4 ^ k * R k ^ 2 * m := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
            have hp : (2 : ℝ) ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
            calc
              2 ^ k * (2 ^ k * R k ^ 2) * m = (2 ^ k * 2 ^ k) * R k ^ 2 * m := by ring
              _ = _ := by rw [hp]
      exact hnext.trans (by rw [hRstep]; linarith [hRnonneg k])
  intro k hkj r hr x hx
  rw [← iteratedFDerivWithin_of_isOpen r hU hx]
  exact hFw k hkj r hr x hx

end GlobalEmbedding.Paper
