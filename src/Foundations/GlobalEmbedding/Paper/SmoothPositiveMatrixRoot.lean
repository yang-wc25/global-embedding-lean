import GlobalEmbedding.Paper.SymmetricPositiveRootSylvester
import GlobalEmbedding.Paper.PositiveMatrixConeOpen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.Star

/-!
# Smoothness of the actual positive matrix root

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, proof line 798. Squaring on the symmetric matrix space has
invertible derivative `Z ↦ PZ+ZP` at every positive `P`. Its smooth local inverse
stays positive and is the actual CFC square root by nonnegative-root uniqueness.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff Topology

namespace GlobalEmbedding.Paper

open Matrix Filter

/-- The actual CFC positive root is smooth on the positive symmetric cone; its
inverse matrix is smooth too. Its derivative is the inverse of the genuine
Sylvester equivalence at the root. Pointwise positivity, the square identity and
uniqueness are included. The proof uses the smooth inverse-function theorem on
the symmetric subspace and identifies its positive inverse germ by CFC uniqueness.
Source: positive metric square-root normalization in `prop:initialization`. -/
theorem smooth_positive_matrix_root
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : selfAdjoint.submodule ℝ (Matrix n n ℝ)) (hA : (A : Matrix n n ℝ).PosDef) :
    let S := selfAdjoint.submodule ℝ (Matrix n n ℝ)
    let R : S → Matrix n n ℝ := fun B ↦ CFC.sqrt (B : Matrix n n ℝ)
    (R A).PosDef ∧ (R A) ^ 2 = (A : Matrix n n ℝ) ∧
      (∀ B : Matrix n n ℝ, B.PosDef → B ^ 2 = (A : Matrix n n ℝ) → B = R A) ∧
      ContDiffAt ℝ ∞ R A ∧ ContDiffAt ℝ ∞ (fun B ↦ (R B)⁻¹) A ∧
      ∃ L : S ≃L[ℝ] S,
        (∀ Z, (L Z : Matrix n n ℝ) = R A * (Z : Matrix n n ℝ) +
          (Z : Matrix n n ℝ) * R A) ∧
        HasFDerivAt R (S.subtypeL.comp L.symm.toContinuousLinearMap) A := by
  dsimp only
  let S := selfAdjoint.submodule ℝ (Matrix n n ℝ)
  let R : S → Matrix n n ℝ := fun B ↦ CFC.sqrt (B : Matrix n n ℝ)
  let Q : S := ⟨R A, (CFC.sqrt_nonneg (A : Matrix n n ℝ)).posSemidef.isHermitian⟩
  have hQ : (Q : Matrix n n ℝ).PosDef :=
    (IsStrictlyPositive.sqrt (A : Matrix n n ℝ) hA.isStrictlyPositive).posDef
  obtain ⟨L, hL⟩ := positive_symmetric_sylvester_equiv_exists hQ
  let proj : Matrix n n ℝ →L[ℝ] S :=
    (((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (Matrix n n ℝ) +
      (starL' ℝ : Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ).toContinuousLinearMap)).codRestrict S (by
        intro X
        change star ((2 : ℝ)⁻¹ • (X + star X)) = (2 : ℝ)⁻¹ • (X + star X)
        simp only [star_smul, star_trivial, star_add, star_star]
        rw [add_comm])
  let inc := S.subtypeL
  let sq : S → S := fun X ↦ proj ((X : Matrix n n ℝ) * X)
  have hp (X : Matrix n n ℝ) (hX : IsSelfAdjoint X) : (proj X : Matrix n n ℝ) = X := by
    change (2 : ℝ)⁻¹ • (X + star X) = X
    rw [hX.star_eq, ← two_smul ℝ X, smul_smul]
    norm_num
  have hv (X : S) : (sq X : Matrix n n ℝ) = (X : Matrix n n ℝ) * X := by
    apply hp
    change star ((X : Matrix n n ℝ) * X) = _
    rw [star_mul, X.property]
  have hs : ContDiff ℝ ∞ sq := proj.contDiff.comp (inc.contDiff.mul inc.contDiff)
  have hd : HasFDerivAt sq (L : S →L[ℝ] S) Q := by
    have hc := inc.hasFDerivAt (x := Q)
    have h := proj.hasFDerivAt.comp Q (hc.mul' hc)
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    intro Z
    apply Subtype.ext
    change (proj ((Q : Matrix n n ℝ) * Z + (Z : Matrix n n ℝ) * Q) : Matrix n n ℝ) =
      (L Z : Matrix n n ℝ)
    rw [hL]
    apply hp
    change star ((Q : Matrix n n ℝ) * Z + (Z : Matrix n n ℝ) * Q) = _
    rw [star_add, star_mul, star_mul, Q.property, Z.property]
    exact add_comm _ _
  have hQA : sq Q = A := by
    apply Subtype.ext
    rw [hv]
    exact CFC.sqrt_mul_sqrt_self (A : Matrix n n ℝ) hA.posSemidef.nonneg
  have hstrict := hs.contDiffAt.hasStrictFDerivAt' hd (by simp)
  let inv : S → S := hs.contDiffAt.localInverse hd (by simp)
  have hInv : ContDiffAt ℝ ∞ inv A := by
    simpa only [hQA] using hs.contDiffAt.to_localInverse hd (by simp)
  have hbase : inv A = Q := by
    simpa only [hQA] using hs.contDiffAt.localInverse_apply_image hd (by simp)
  have hright : ∀ᶠ B in 𝓝 A, sq (inv B) = B := by
    simpa only [hQA, inv, ContDiffAt.localInverse] using! hstrict.eventually_right_inverse
  have hpos : ∀ᶠ B in 𝓝 A, (inv B : Matrix n n ℝ).PosDef := by
    have hmem := (isOpen_positive_symmetric_matrices (n := n)).mem_nhds hQ
    have ht := hInv.continuousAt
    change Tendsto inv (𝓝 A) (𝓝 (inv A)) at ht
    rw [hbase] at ht
    exact ht hmem
  have hEq : R =ᶠ[𝓝 A] fun B ↦ (inv B : Matrix n n ℝ) := by
    filter_upwards [hright, hpos] with B hB hpB
    apply CFC.sqrt_unique _ hpB.posSemidef.nonneg
    exact (hv (inv B)).symm.trans (congrArg Subtype.val hB)
  have hR : ContDiffAt ℝ ∞ R A :=
    (inc.contDiff.contDiffAt.comp A hInv).congr_of_eventuallyEq hEq
  have hRi : ContDiffAt ℝ ∞ (fun B ↦ (R B)⁻¹) A := by
    have hu : IsUnit (R A) := hQ.isUnit
    have hi := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using! hi.comp A hR
  have hInvDeriv : HasFDerivAt inv (L.symm : S →L[ℝ] S) A := by
    simpa only [hQA, inv, ContDiffAt.localInverse] using! hstrict.to_localInverse.hasFDerivAt
  have hRDeriv : HasFDerivAt R (inc.comp L.symm.toContinuousLinearMap) A :=
    ((inc.hasFDerivAt).comp A hInvDeriv).congr_of_eventuallyEq hEq
  refine ⟨hQ, CFC.sq_sqrt _ hA.posSemidef.nonneg, ?_, hR, hRi, L, hL, hRDeriv⟩
  intro B hB hBA
  exact (CFC.sqrt_unique (by simpa only [pow_two] using hBA) hB.posSemidef.nonneg).symm

#print axioms smooth_positive_matrix_root

end GlobalEmbedding.Paper
