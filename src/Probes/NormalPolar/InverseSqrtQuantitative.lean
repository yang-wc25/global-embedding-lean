import NormalPolar.CompressionQuantitative

/-!
# Explicit bounds for the actual positive inverse square root

The actual H from the binomial construction satisfies H² = G.inverse and
H >= I on the old normal fiber. Its norm and quadratic difference from
identity follow from the true compression reserve and coercivity of H + I.
No independently selected square root is introduced.
-/

noncomputable section
open Set
open scoped ContDiff

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Continuation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private noncomputable local instance sqrtQuantFiberSemi (K : Submodule ℝ V) :
    SeminormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance sqrtQuantFiberNormed (K : Submodule ℝ V) :
    NormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance sqrtQuantFiberSpace (K : Submodule ℝ V) :
    NormedSpace ℝ (K →L[ℝ] K) := ContinuousLinearMap.toNormedSpace

/-- Self-adjointness identifies the squared native operator norm with the
norm of the already constructed true compression inverse. -/
theorem actualNormalInverseSqrt_norm_sq
    (K L : Submodule ℝ V) (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    ‖actualNormalInverseSqrt K L‖ ^ 2 =
      ‖(normalProjectionCompression K L.starProjection).inverse‖ := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self (actualNormalInverseSqrt K L)
  rw [(actualNormalInverseSqrt_selfAdjoint K L).adjoint_eq] at h
  change ‖actualNormalInverseSqrt K L * actualNormalInverseSqrt K L‖ = _ at h
  rw [actualNormalInverseSqrt_sq_eq_inverse K L hclose] at h
  simpa only [pow_two] using h.symm

/-- An explicit inverse-square-root norm bound on the genuine projection
reserve, valid also when the normal fiber is zero dimensional. -/
theorem actualNormalInverseSqrt_norm_le
    (K L : Submodule ℝ V) (q : ℝ) (hq : q < 1)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ q) :
    ‖actualNormalInverseSqrt K L‖ ≤ Real.sqrt ((1 - q ^ 2)⁻¹) := by
  apply Real.le_sqrt_of_sq_le
  rw [actualNormalInverseSqrt_norm_sq K L (hgap.trans_lt hq)]
  exact (normalProjectionCompression_inverse_quadratic_bound K L q hq hgap).2

/-- H >= I gives a true inverse for H + I with the universal bound 1/2.
This is proved from the explicit construction, rather than assumed as a
functional-calculus regularity property. -/
theorem actualNormalInverseSqrt_add_one_inverse_bound
    (K L : Submodule ℝ V) (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    (actualNormalInverseSqrt K L + 1).IsInvertible ∧
      ‖(actualNormalInverseSqrt K L + 1).inverse‖ ≤ (1 / 2 : ℝ) := by
  have hcoer (v : K) :
      (2 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ v ((actualNormalInverseSqrt K L + 1) v) := by
    change (2 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ v (actualNormalInverseSqrt K L v + v)
    rw [inner_add_right, real_inner_self_eq_norm_sq]
    have h := actualNormalInverseSqrt_coercive K L hclose v
    linarith
  have h := coercive_inverse_smooth_bound (Set.univ : Set ℝ) isOpen_univ
    (fun _ : ℝ ↦ actualNormalInverseSqrt K L + 1) 2 (by norm_num) contDiffOn_const
    (fun _ _ v ↦ hcoer v)
  simpa only [inv_eq_one_div] using h.1 0 (Set.mem_univ 0)

/-- Exact factorization of the positive-root correction through its true
native inverse. It does not assert commutation of unrelated operators. -/
theorem actualNormalInverseSqrt_sub_one_factorization
    (K L : Submodule ℝ V) (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    actualNormalInverseSqrt K L - 1 =
      ((normalProjectionCompression K L.starProjection).inverse - 1) *
        (actualNormalInverseSqrt K L + 1).inverse := by
  let H := actualNormalInverseSqrt K L
  have hH : (H + 1).IsInvertible :=
    (actualNormalInverseSqrt_add_one_inverse_bound K L hclose).1
  have hinv : (H + 1) * (H + 1).inverse = 1 := hH.self_comp_inverse
  have hfactor : (H - 1) * (H + 1) = H * H - 1 := by
    simp only [sub_mul, mul_add, mul_one, one_mul]
    abel
  calc
    H - 1 = (H - 1) * ((H + 1) * (H + 1).inverse) := by rw [hinv, mul_one]
    _ = (H * H - 1) * (H + 1).inverse := by rw [← mul_assoc, hfactor]
    _ = _ := by rw [actualNormalInverseSqrt_sq_eq_inverse K L hclose]

/-- The positive normalization has a quadratic correction with a fully
specified reserve constant, independent of any compactness choice. -/
theorem actualNormalInverseSqrt_sub_one_norm_le
    (K L : Submodule ℝ V) (q : ℝ) (hq : q < 1)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ q) :
    ‖actualNormalInverseSqrt K L - 1‖ ≤
      ((1 / 2 : ℝ) * (1 - q ^ 2)⁻¹) * ‖K.starProjection - L.starProjection‖ ^ 2 := by
  rw [actualNormalInverseSqrt_sub_one_factorization K L (hgap.trans_lt hq)]
  have hroot := actualNormalInverseSqrt_add_one_inverse_bound K L (hgap.trans_lt hq)
  have hinv := normalProjectionCompression_inverse_gap_on_reserve K L q hq hgap
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hgap
  have hq2 : q ^ 2 < 1 := by nlinarith
  calc
    _ ≤ ‖(normalProjectionCompression K L.starProjection).inverse - 1‖ *
        ‖(actualNormalInverseSqrt K L + 1).inverse‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((1 - q ^ 2)⁻¹ * ‖K.starProjection - L.starProjection‖ ^ 2) * (1 / 2 : ℝ) :=
      mul_le_mul hinv hroot.2 (norm_nonneg _)
        (mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hq2.le)) (sq_nonneg _))
    _ = _ := by ring

end GlobalEmbedding.NormalPolar
