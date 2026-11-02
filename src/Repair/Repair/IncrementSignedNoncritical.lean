import Repair.ReferenceSignedReserve

/-!
# The same hierarchical signed phases have a numerical noncritical reserve

The original template good ball excludes the zero covector.  The moving
reserve radius was reduced to half that ball, so the actual hierarchy
also gives a common lower bound on the spatial differential norm.  This
is the input used by the genuine scalar inverse-function construction.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
open scoped TensorProduct Topology Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance noncriticalRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance noncriticalSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}

theorem increment_template_covector_norm_lower
    (C : UniformActualGoodDictionaryCover K) (i : C.indices)
    (a : EdgePair (Module.finrank ℝ E+1)) :
    C.covectorRadius ≤ ‖(C.template i).covectors a‖ := by
  by_contra! h
  have hz := (C.template i).covector_ball_control i.val.val.1 (C.centers i).1 a 0
    (by simpa only [zero_sub,norm_neg] using h.trans_le (C.bounds i).2.2.1)
  exact hz.1 rfl

theorem increment_normalized_signed_norm_lower
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) (i : C.indices)
    (a : EdgePair (Module.finrank ℝ E+1)) (eta : E →L[ℝ] ℝ) (w : ℝ)
    (hw : 1 ≤ |w|)
    (hClose : ‖w⁻¹ • eta-(C.template i).covectors a‖ < incrementUniformSignedRadius C R) :
    C.covectorRadius/2 ≤ ‖eta‖ := by
  have hRadius := incrementUniformSignedRadius_le_half C R
  have hCenter := increment_template_covector_norm_lower C i a
  have hSmall : ‖(C.template i).covectors a-w⁻¹ • eta‖ < C.covectorRadius/2 := by
    rw [norm_sub_rev]
    exact hClose.trans_le hRadius
  have hLower : C.covectorRadius/2 ≤ ‖w⁻¹ • eta‖ := by
    have h := norm_le_norm_add_norm_sub (w⁻¹ • eta) ((C.template i).covectors a)
    rw [norm_sub_rev] at h
    linarith
  have hw0 : 0 < |w| := zero_lt_one.trans_le hw
  have hi : |w⁻¹| ≤ 1 := by
    rw [abs_inv]
    exact (inv_le_one₀ hw0).mpr hw
  have hScale : ‖w⁻¹ • eta‖ ≤ ‖eta‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hi (norm_nonneg eta)).trans_eq (one_mul _)
  exact hLower.trans hScale

theorem increment_signed_foreign_noncritical
    (C : UniformActualGoodDictionaryCover K) (R transitionBound : ℝ) (hT : 0 ≤ transitionBound)
    (dominant foreign : C.indices)
    (a b : EdgePair (Module.finrank ℝ E+1))
    (transition : E →L[ℝ] E) (htransition : ‖transition‖ ≤ transitionBound)
    {i j : ℕ} (hij : i < j) :
    let w := repairReferenceSignedHierarchy C R transitionBound
    C.covectorRadius/2 ≤ ‖w^j • (C.template dominant).covectors a+
      w^i • ((C.template foreign).covectors b).comp transition‖ ∧
    C.covectorRadius/2 ≤ ‖w^j • (C.template dominant).covectors a-
      w^i • ((C.template foreign).covectors b).comp transition‖ := by
  intro w
  have hw : 1 < w := repairReferenceSignedHierarchy_gt_one C R transitionBound hT
  have hPow : 1 ≤ |w^j| := by
    rw [abs_of_nonneg (pow_nonneg (zero_lt_one.trans hw).le j)]
    exact one_le_pow₀ hw.le
  have hforeign : ‖((C.template foreign).covectors b).comp transition‖ ≤ C.covectorBound*transitionBound :=
    (((C.template foreign).covectors b).opNorm_comp_le transition).trans
      (mul_le_mul ((C.bounds foreign).2.2.2.2 b) htransition (norm_nonneg _) C.covectorBound_pos.le)
  have hClose := repair_reference_hierarchy_normalized_close
    (incrementUniformSignedRadius_pos C R) (mul_nonneg C.covectorBound_pos.le hT)
    (((C.template foreign).covectors b).comp transition) ((C.template dominant).covectors a) hforeign hij
  exact ⟨increment_normalized_signed_norm_lower C R dominant a _ _ hPow hClose.1,
    increment_normalized_signed_norm_lower C R dominant a _ _ hPow hClose.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_signed_foreign_noncritical
