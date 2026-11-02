import Upgrade.RankQSchur
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Schur zero set is the actual rank-q locus

The kernel graph below is built from the same fixed section of the actual
reference range. It gives the exact rank decomposition, including rectangular
forms. No rank equation or incidence rank is supplied as a hypothesis.
-/

noncomputable section
namespace GlobalEmbedding.Upgrade

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- Projection to the actual kernel along the selected actual range section. -/
def rankQKernelProjection (B : S →L[ℝ] W) : S →L[ℝ] B.ker :=
  (ContinuousLinearMap.id ℝ S - (rankQRangeSection B).comp B.rangeRestrict).codRestrict
    B.ker (by
      intro z
      change B (z - rankQRangeSection B (B.rangeRestrict z)) = 0
      rw [map_sub, rankQRangeSection_apply]
      exact sub_self (B z))

@[simp] theorem rankQKernelProjection_coe (B : S →L[ℝ] W) (z : S) :
    (rankQKernelProjection B z : S) = z - rankQRangeSection B (B.rangeRestrict z) := rfl

@[simp] theorem rankQKernelProjection_kernel (B : S →L[ℝ] W) (k : B.ker) :
    rankQKernelProjection B k = k := by
  apply Subtype.ext
  have hk : B (k : S) = 0 := k.property
  have hkr : B.rangeRestrict k = 0 := Subtype.ext hk
  simp [hkr]

@[simp] theorem rankQKernelProjection_section (B : S →L[ℝ] W) (r : B.range) :
    rankQKernelProjection B (rankQRangeSection B r) = 0 := by
  apply Subtype.ext
  have hr : B.rangeRestrict (rankQRangeSection B r) = r :=
    DFunLike.congr_fun (rankQRangeSection_spec B) r
  simp [hr]

/-- The actual graph over the original kernel determined by the upper block equation. -/
def rankQKernelGraph (B C : S →L[ℝ] W) : B.ker →L[ℝ] S :=
  B.ker.subtypeL - (rankQRangeSection B).comp
    ((rankQBlockA B C).inverse.comp (rankQBlockN B C))

@[simp] theorem rankQKernelProjection_graph (B C : S →L[ℝ] W) (k : B.ker) :
    rankQKernelProjection B (rankQKernelGraph B C k) = k := by
  change rankQKernelProjection B
    ((k : S) - rankQRangeSection B ((rankQBlockA B C).inverse (rankQBlockN B C k))) = k
  simp

theorem rankQKernelGraph_range_block (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) (k : B.ker) :
    B.range.orthogonalProjectionOnto (C (rankQKernelGraph B C k)) = 0 := by
  change B.range.orthogonalProjectionOnto
    (C ((k : S) - rankQRangeSection B ((rankQBlockA B C).inverse (rankQBlockN B C k)))) = 0
  rw [map_sub, map_sub]
  change rankQBlockN B C k - rankQBlockA B C ((rankQBlockA B C).inverse (rankQBlockN B C k)) = 0
  rw [hA.self_apply_inverse, sub_self]

theorem rankQKernelGraph_normal_block (B C : S →L[ℝ] W) (k : B.ker) :
    B.rangeᗮ.orthogonalProjectionOnto (C (rankQKernelGraph B C k)) = rankQSchur B C k := by
  change B.rangeᗮ.orthogonalProjectionOnto
    (C ((k : S) - rankQRangeSection B ((rankQBlockA B C).inverse (rankQBlockN B C k)))) = _
  rw [map_sub, map_sub]
  rfl

theorem rankQKernelGraph_mem_ker_iff (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) (k : B.ker) :
    C (rankQKernelGraph B C k) = 0 ↔ rankQSchur B C k = 0 := by
  constructor
  · intro hk
    rw [← rankQKernelGraph_normal_block, hk, map_zero]
  · intro hk
    have hr := rankQKernelGraph_range_block B C hA k
    have hl := rankQKernelGraph_normal_block B C k
    rw [hk] at hl
    have hd := B.range.starProjection_add_starProjection_orthogonal (C (rankQKernelGraph B C k))
    have hr' : B.range.starProjection (C (rankQKernelGraph B C k)) = 0 :=
      congrArg Subtype.val hr
    have hl' : B.rangeᗮ.starProjection (C (rankQKernelGraph B C k)) = 0 :=
      congrArg Subtype.val hl
    rw [hr', hl', zero_add] at hd
    exact hd.symm

theorem rankQKernelGraph_projection_of_mem_ker (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) (z : S) (hz : C z = 0) :
    rankQKernelGraph B C (rankQKernelProjection B z) = z := by
  have hsplit : rankQRangeSection B (B.rangeRestrict z) +
      (rankQKernelProjection B z : S) = z := by simp
  have heq : rankQBlockA B C (B.rangeRestrict z) +
      rankQBlockN B C (rankQKernelProjection B z) = 0 := by
    change B.range.orthogonalProjectionOnto (C (rankQRangeSection B (B.rangeRestrict z))) +
      B.range.orthogonalProjectionOnto (C (rankQKernelProjection B z)) = 0
    rw [← map_add, ← map_add, hsplit, hz, map_zero]
  have hInv : (rankQBlockA B C).inverse (rankQBlockN B C (rankQKernelProjection B z)) =
      -(B.rangeRestrict z) := by
    have hn : rankQBlockN B C (rankQKernelProjection B z) =
        -(rankQBlockA B C (B.rangeRestrict z)) := (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using heq)
    rw [hn, map_neg, hA.inverse_apply_self]
  change (rankQKernelProjection B z : S) - rankQRangeSection B
    ((rankQBlockA B C).inverse (rankQBlockN B C (rankQKernelProjection B z))) = z
  rw [hInv, map_neg, sub_neg_eq_add, add_comm]
  exact hsplit

/-- The kernel of the nearby form is exactly the graph of the kernel of its Schur residual. -/
def rankQSchurKernelEquiv (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) : (rankQSchur B C).ker ≃ₗ[ℝ] C.ker where
  toFun k := ⟨rankQKernelGraph B C k,
    (rankQKernelGraph_mem_ker_iff B C hA k).mpr k.property⟩
  invFun z := ⟨rankQKernelProjection B z,
    (rankQKernelGraph_mem_ker_iff B C hA _).mp (by
      rw [rankQKernelGraph_projection_of_mem_ker B C hA z z.property]
      exact z.property)⟩
  left_inv k := by apply Subtype.ext; exact rankQKernelProjection_graph B C k
  right_inv z := by apply Subtype.ext; exact rankQKernelGraph_projection_of_mem_ker B C hA z z.property
  map_add' k l := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a k := by apply Subtype.ext; exact map_smul _ _ _

/-- Exact rank decomposition in the actual fixed Schur chart. -/
theorem rankQSchur_finrank_range (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) :
    Module.finrank ℝ C.range = Module.finrank ℝ B.range +
      Module.finrank ℝ (rankQSchur B C).range := by
  have hker := (rankQSchurKernelEquiv B C hA).finrank_eq
  have hC := C.toLinearMap.finrank_range_add_finrank_ker
  have hB := B.toLinearMap.finrank_range_add_finrank_ker
  have hR := (rankQSchur B C).toLinearMap.finrank_range_add_finrank_ker
  omega

/-- The zero set of the literal residual is precisely the original rank stratum. -/
theorem rankQSchur_eq_zero_iff_rank (B C : S →L[ℝ] W)
    (hA : (rankQBlockA B C).IsInvertible) :
    rankQSchur B C = 0 ↔ Module.finrank ℝ C.range = Module.finrank ℝ B.range := by
  rw [rankQSchur_finrank_range B C hA]
  constructor
  · intro h
    simp [h]
  · intro h
    have hz : Module.finrank ℝ (rankQSchur B C).range = 0 := by omega
    have hr : (rankQSchur B C).toLinearMap.range = ⊥ := Submodule.finrank_eq_zero.mp hz
    apply ContinuousLinearMap.coe_injective
    exact LinearMap.range_eq_bot.mp hr

end GlobalEmbedding.Upgrade
