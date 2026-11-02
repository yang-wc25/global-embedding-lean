import Smoothing.WeightedActualInverse
import Smoothing.WeightedCoerciveInverse

/-! The original inverse derivative recurrence is used on arbitrary samples
inside its genuine open smooth/invertible domain. Only the quantitative value
and derivative bounds are sampled. This keeps compact parameter boundaries
inside the original differentiation neighborhood without strengthening bounds
on that neighborhood or changing the majorant. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

theorem actual_inverse_derivative_bounds_on_samples
    {D A : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (j : ℕ) (U S : Set D) (hU : IsOpen U) (hSU : S ⊆ U) (P : D → A)
    (hP : ContDiffOn ℝ ∞ P U) (hunit : ∀ x ∈ U, IsUnit (P x))
    (b m : ℝ) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hval : ∀ x ∈ S, ‖Ring.inverse (P x)‖ ≤ b)
    (hder : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ S, ‖iteratedFDeriv ℝ k P x‖ ≤ m)
    (R : ℕ → ℝ) (hR0 : R 0 = 1 + b)
    (hRstep : ∀ k, R (k + 1) = R k + 4 ^ k * R k ^ 2 * m) :
    ∀ k ≤ j, ∀ r ≤ k, ∀ x ∈ S,
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
  have hFw : ∀ k ≤ j, ∀ r ≤ k, ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ r F U x‖ ≤ R k := by
    intro k
    induction k with
    | zero =>
      intro hkj r hr x hx
      have hxO : x ∈ U := hSU hx
      have : r = 0 := by omega
      subst r
      rw [norm_iteratedFDerivWithin_zero]
      exact (hval x hx).trans (by rw [hR0]; linarith)
    | succ k hk =>
      intro hkj r hr x hx
      have hxO : x ∈ U := hSU hx
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
          |>.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hF hF hU.uniqueDiffOn hxO
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
        rw [← norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hxO]
        rw [iteratedFDerivWithin_congr hDF hxO]
        change ‖iteratedFDerivWithin ℝ k
          (-(fun y ↦ (H y).comp (fderivWithin ℝ P U y))) U x‖ ≤ _
        rw [iteratedFDerivWithin_neg_apply hU.uniqueDiffOn hxO, norm_neg]
        have he := (ContinuousLinearMap.compL ℝ D A A)
          |>.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hH hDP hU.uniqueDiffOn hxO
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
              rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hxO,
                iteratedFDerivWithin_of_isOpen _ hU hxO]
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
  have hxO : x ∈ U := hSU hx
  rw [← iteratedFDerivWithin_of_isOpen r hU hxO]
  exact hFw k hkj r hr x hx


theorem actual_inverse_slow_weighted_jets_on_samples
    {D A : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O) (P : D → A)
    (hP : ContDiffOn ℝ ∞ P O) (hunit : ∀ x ∈ O, IsUnit (P x))
    (ell b M : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hval : ∀ x ∈ S, ‖Ring.inverse (P x)‖ ≤ b)
    (hjet : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k P x‖ ≤ M) :
    ∀ k ≤ j, ∀ r ≤ k, ∀ x ∈ S,
      ell ^ r * ‖iteratedFDeriv ℝ r (fun y => Ring.inverse (P y)) x‖ ≤
        slowInverseMajorant b M k := by
  let e := slowDilation (D := D) ell hell.ne'
  let V := e ⁻¹' O
  let T := e ⁻¹' S
  let Q := P ∘ e
  have hV : IsOpen V := hO.preimage e.continuous
  have hQ : ContDiffOn ℝ ∞ Q V := hP.comp e.contDiff.contDiffOn (fun _ hy => hy)
  have hQunit : ∀ x ∈ V, IsUnit (Q x) := fun x hx => hunit (e x) hx
  have hQval : ∀ x ∈ T, ‖Ring.inverse (Q x)‖ ≤ b := fun x hx => hval (e x) hx
  have hQjet : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ T, ‖iteratedFDeriv ℝ k Q x‖ ≤ M := by
    intro k hk hkj x hx
    rw [norm_iteratedFDeriv_slowDilation P ell hell k x]
    exact hjet k hk hkj (e x) hx
  have hi := actual_inverse_derivative_bounds_on_samples j V T hV (fun _ hx => hSO hx) Q hQ hQunit b M hb hM hQval hQjet
    (slowInverseMajorant b M) rfl (fun _ => rfl)
  intro k hkj r hr x hx
  have hx' : e.symm x ∈ T := by
    change e (e.symm x) ∈ S
    simpa only [e.apply_symm_apply] using hx
  have h := hi k hkj r hr (e.symm x) hx'
  change ‖iteratedFDeriv ℝ r ((fun y => Ring.inverse (P y)) ∘ e) (e.symm x)‖ ≤ _ at h
  rw [norm_iteratedFDeriv_slowDilation _ ell hell r (e.symm x)] at h
  have he : ell • e.symm x = x := e.apply_symm_apply x
  rwa [he] at h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_inverse_derivative_bounds_on_samples
#print axioms GlobalEmbedding.Continuation.actual_inverse_slow_weighted_jets_on_samples
