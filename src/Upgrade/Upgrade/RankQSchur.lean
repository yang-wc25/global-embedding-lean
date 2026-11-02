import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schur equations in the actual kernel and range of a second form

Source: `thm:upgrade`, the rank-q incidence (10.1).  The domain below is
allowed to be the paper's original symmetric-square quotient: no inner product
on that quotient is introduced.  The complement is selected by a right inverse
of the actual range restriction.  Thus the invertible reference block is the
identity on the actual range, and the residual has exactly the original
kernel-to-range-perpendicular type.

This is an internal geometric construction, not the embedding-upgrade theorem.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Upgrade

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- A genuine right inverse of the range restriction of the reference form. -/
def rankQRangeSection (B : S →L[ℝ] W) : B.range →L[ℝ] S :=
  Classical.choose (B.rangeRestrict.exists_rightInverse_of_surjective (by simp))

theorem rankQRangeSection_spec (B : S →L[ℝ] W) :
    B.rangeRestrict.comp (rankQRangeSection B) = ContinuousLinearMap.id ℝ B.range :=
  Classical.choose_spec (B.rangeRestrict.exists_rightInverse_of_surjective (by simp))

@[simp] theorem rankQRangeSection_apply (B : S →L[ℝ] W) (v : B.range) :
    B (rankQRangeSection B v) = (v : W) := by
  exact congrArg Subtype.val (DFunLike.congr_fun (rankQRangeSection_spec B) v)

/-- The actual top-left block; its reference value is the identity. -/
def rankQBlockA (B C : S →L[ℝ] W) : B.range →L[ℝ] B.range :=
  B.range.orthogonalProjectionOnto.comp (C.comp (rankQRangeSection B))

/-- The top-right block on the SAME actual kernel. -/
def rankQBlockN (B C : S →L[ℝ] W) : B.ker →L[ℝ] B.range :=
  B.range.orthogonalProjectionOnto.comp (C.comp B.ker.subtypeL)

/-- The lower-left block in the SAME actual normal complement. -/
def rankQBlockM (B C : S →L[ℝ] W) : B.range →L[ℝ] B.rangeᗮ :=
  B.rangeᗮ.orthogonalProjectionOnto.comp (C.comp (rankQRangeSection B))

/-- The lower-right block on the actual kernel and actual normal complement. -/
def rankQBlockD (B C : S →L[ℝ] W) : B.ker →L[ℝ] B.rangeᗮ :=
  B.rangeᗮ.orthogonalProjectionOnto.comp (C.comp B.ker.subtypeL)

/-- Literal Schur residual of the nearby actual form in the fixed reference split. -/
def rankQSchur (B C : S →L[ℝ] W) : B.ker →L[ℝ] B.rangeᗮ :=
  rankQBlockD B C - (rankQBlockM B C).comp
    ((rankQBlockA B C).inverse.comp (rankQBlockN B C))

@[simp] theorem rankQBlockA_self (B : S →L[ℝ] W) :
    rankQBlockA B B = ContinuousLinearMap.id ℝ B.range := by
  ext v
  simp [rankQBlockA]

@[simp] theorem rankQBlockN_self (B : S →L[ℝ] W) : rankQBlockN B B = 0 := by
  ext v
  have hv : B (v : S) = 0 := v.property
  simp [rankQBlockN, hv]

@[simp] theorem rankQBlockM_self (B : S →L[ℝ] W) : rankQBlockM B B = 0 := by
  ext v
  simp only [rankQBlockM, ContinuousLinearMap.comp_apply, rankQRangeSection_apply,
    ContinuousLinearMap.zero_apply]
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    (B.range.le_orthogonal_orthogonal v.property))

@[simp] theorem rankQBlockD_self (B : S →L[ℝ] W) : rankQBlockD B B = 0 := by
  ext v
  have hv : B (v : S) = 0 := v.property
  simp [rankQBlockD, hv]

@[simp] theorem rankQSchur_self (B : S →L[ℝ] W) : rankQSchur B B = 0 := by
  simp [rankQSchur]

theorem rankQBlockA_contDiff (B : S →L[ℝ] W) : ContDiff ℝ ∞ (rankQBlockA B) := by
  exact contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem rankQBlockN_contDiff (B : S →L[ℝ] W) : ContDiff ℝ ∞ (rankQBlockN B) := by
  exact contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem rankQBlockM_contDiff (B : S →L[ℝ] W) : ContDiff ℝ ∞ (rankQBlockM B) := by
  exact contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem rankQBlockD_contDiff (B : S →L[ℝ] W) : ContDiff ℝ ∞ (rankQBlockD B) := by
  exact contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

/-- Smoothness holds on the actual invertible-block domain. -/
theorem rankQSchur_contDiffAt (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) : ContDiffAt ℝ ∞ (rankQSchur B) C := by
  have hi := hA.contDiffAt_map_inverse.comp C (rankQBlockA_contDiff B).contDiffAt
  exact (rankQBlockD_contDiff B).contDiffAt.sub
    ((rankQBlockM_contDiff B).contDiffAt.clm_comp
      (hi.clm_comp (rankQBlockN_contDiff B).contDiffAt))

/-- The reference point lies in the actual smooth Schur chart. -/
theorem rankQSchur_contDiffAt_self (B : S →L[ℝ] W) :
    ContDiffAt ℝ ∞ (rankQSchur B) B := by
  apply rankQSchur_contDiffAt
  rw [rankQBlockA_self]
  exact ⟨ContinuousLinearEquiv.refl ℝ B.range, rfl⟩

end GlobalEmbedding.Upgrade
