import NormalPolar.ConstructionCompression
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
Positivity selects the actual positive inverse-square-root branch.  Every
coefficient of the series in `(P-R)^2` is a positive multichoose coefficient;
each even power of the self-adjoint difference is positive. The zero-th term
therefore gives a coercivity constant of one for this concrete construction.
-/

noncomputable section
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation

theorem multichoose_half_pos (n : ℕ) : 0 < Ring.multichoose (1 / 2 : ℝ) n := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
  have hpos := ascPochhammer_pos n (1 / 2 : ℝ) (by norm_num)
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  nlinarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem actualInvSqrt_term_eq_multichoose (E : V →L[ℝ] V) (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n • (-E) ^ n = Ring.multichoose (1 / 2 : ℝ) n • E ^ n := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Ring.choose_neg']
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  rw [← neg_one_smul ℝ E, smul_pow, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (Ring.multichoose (1 / 2 : ℝ) n), ← mul_assoc, ← mul_pow]
  norm_num

theorem projectionDefect_pow_positive (P R : V →L[ℝ] V)
    (hP : IsSelfAdjoint P) (hR : IsSelfAdjoint R) (n : ℕ) :
    (projectionDefect P R ^ n).IsPositive := by
  have h := ContinuousLinearMap.isPositive_self_comp_adjoint ((P - R) ^ n)
  rw [((hP.sub hR).pow n).adjoint_eq] at h
  have he : projectionDefect P R ^ n = (P - R) ^ n * (P - R) ^ n := by
    rw [projectionDefect, ← pow_mul, show 2 * n = n + n by omega, pow_add]
  rw [he]
  exact h

theorem actualInvSqrt_defect_term_positive (P R : V →L[ℝ] V)
    (hP : IsSelfAdjoint P) (hR : IsSelfAdjoint R) (n : ℕ) :
    (Ring.choose (-1 / 2 : ℝ) n • (-projectionDefect P R) ^ n).IsPositive := by
  rw [actualInvSqrt_term_eq_multichoose]
  exact (projectionDefect_pow_positive P R hP hR n).smul_of_nonneg (multichoose_half_pos n).le

theorem actualInvSqrt_defect_coercive (P R : V →L[ℝ] V)
    (hP : IsSelfAdjoint P) (hR : IsSelfAdjoint R) (hclose : ‖P - R‖ < 1) (v : V) :
    ‖v‖ ^ 2 ≤ inner ℝ v (actualInvSqrt (projectionDefect P R) v) := by
  let J : (V →L[ℝ] V) →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ V v)
  let f : ℕ → V →L[ℝ] V := fun n ↦ Ring.choose (-1 / 2 : ℝ) n • (-projectionDefect P R) ^ n
  have hf : Summable f := (summable_norm_actualInvSqrt _ (norm_sub_sq_lt_one P R hclose)).of_norm
  have hsum : HasSum (fun n ↦ J (f n)) (J (actualInvSqrt (projectionDefect P R))) := by
    rw [actualInvSqrt_eq_tsum]
    exact J.hasSum hf.hasSum
  have hnonneg (n : ℕ) : 0 ≤ J (f n) :=
    (actualInvSqrt_defect_term_positive P R hP hR n).inner_nonneg_right v
  have hh := hsum.summable.le_tsum 0 (fun n _ ↦ hnonneg n)
  rw [hsum.tsum_eq] at hh
  simpa [J, f, real_inner_self_eq_norm_sq] using hh

theorem actualInvSqrt_defect_positive (P R : V →L[ℝ] V)
    (hP : IsSelfAdjoint P) (hR : IsSelfAdjoint R) (hclose : ‖P - R‖ < 1) :
    (actualInvSqrt (projectionDefect P R)).IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨
    (actualInvSqrt_selfAdjoint _ (projectionDefect_selfAdjoint P R hP hR)).isSymmetric, ?_⟩
  intro v
  rw [real_inner_comm]
  exact (sq_nonneg ‖v‖).trans (actualInvSqrt_defect_coercive P R hP hR hclose v)

variable [FiniteDimensional ℝ V]

theorem actualNormalInverseSqrt_coercive (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) (v : K) :
    ‖v‖ ^ 2 ≤ inner ℝ v (actualNormalInverseSqrt K L v) := by
  change ‖(v : V)‖ ^ 2 ≤ inner ℝ v (actualNormalInverseSqrt K L v)
  simpa only [actualNormalInverseSqrt, normalProjectionCompression,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using
    actualInvSqrt_defect_coercive K.starProjection L.starProjection
      (isSelfAdjoint_starProjection K) (isSelfAdjoint_starProjection L) hclose (v : V)

theorem actualNormalInverseSqrt_positive (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    (actualNormalInverseSqrt K L).IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨
    (actualNormalInverseSqrt_selfAdjoint K L).isSymmetric, ?_⟩
  intro v
  rw [real_inner_comm]
  exact (sq_nonneg ‖v‖).trans (actualNormalInverseSqrt_coercive K L hclose v)

end GlobalEmbedding.NormalPolar
