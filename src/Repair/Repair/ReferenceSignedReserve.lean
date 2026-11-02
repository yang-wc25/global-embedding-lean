import Repair.ReferenceForeignPhaseTransport
import Repair.IncrementUniformSignedReserve

/-!
# The actual hierarchy produces the uniform signed-kernel reserve

The moving-kernel radius is chosen from the fixed numerical template cover
and operator bound.  The hierarchy is then chosen from that radius, the
same cover's covector bound, and the original first transition bound.
The actual signed covectors, including the foreign transition, satisfy
the required normalized-ball estimate by construction.  No closeness or
signed-reserve hypothesis on the completed phases is left to the caller.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
open scoped TensorProduct Topology
namespace GlobalEmbedding.Continuation

/-- The normalization required by a moving-kernel ball follows from the
literal hierarchy, for both signs and arbitrary distinct ordered labels. -/
theorem repair_reference_hierarchy_normalized_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {radius bound : ℝ} (hr : 0 < radius) (hb : 0 ≤ bound)
    (xi eta : E) (hxi : ‖xi‖ ≤ bound) {i j : ℕ} (hij : i < j) :
    let w := hierarchicalGoodWeight radius bound
    ‖(w^j)⁻¹ • (w^j • eta + w^i • xi)-eta‖ < radius ∧
    ‖(w^j)⁻¹ • (w^j • eta - w^i • xi)-eta‖ < radius := by
  intro w
  have hw : 1 < w := hierarchicalGoodWeight_gt_one hr hb
  have hw0 : 0 < w := zero_lt_one.trans hw
  let r : ℝ := (w^(j-i))⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (pow_nonneg hw0.le _)
  have hp : w ≤ w^(j-i) := by
    simpa only [pow_one] using pow_le_pow_right₀ hw.le (show 1 ≤ j-i by omega)
  have hrle : r ≤ w⁻¹ := (inv_le_inv₀ (pow_pos hw0 _) hw0).mpr hp
  have hpow : w^j=w^i*w^(j-i) := by
    rw [← pow_add,Nat.add_sub_of_le hij.le]
  have hre : w^j*r=w^i := by
    dsimp only [r]
    rw [hpow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hw0.ne'),mul_one]
  have hnorm : ‖r • xi‖ < radius := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
    exact (mul_le_mul hrle hxi (norm_nonneg xi) (inv_nonneg.mpr hw0.le)).trans_lt
      (hierarchicalGoodWeight_small_ratio hr hb)
  have hplus : w^j • (eta+r • xi)=w^j • eta+w^i • xi := by
    rw [smul_add,smul_smul,hre]
  have hminus : w^j • (eta-r • xi)=w^j • eta-w^i • xi := by
    rw [smul_sub,smul_smul,hre]
  constructor
  · rw [← hplus,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ hw0.ne'),one_smul,
      add_sub_cancel_left]
    exact hnorm
  · rw [← hminus,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ hw0.ne'),one_smul,
      sub_sub_cancel_left,norm_neg]
    exact hnorm

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance referenceSignedRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private local instance referenceSignedSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}

/-- This one weight is fixed before the actual map or chart family. -/
def repairReferenceSignedHierarchy (C : UniformActualGoodDictionaryCover K)
    (R transitionBound : ℝ) : ℝ :=
  repairReferenceHierarchy (incrementUniformSignedRadius C R) C.covectorBound transitionBound

theorem repairReferenceSignedHierarchy_gt_one
    (C : UniformActualGoodDictionaryCover K) (R transitionBound : ℝ)
    (hT : 0 ≤ transitionBound) : 1 < repairReferenceSignedHierarchy C R transitionBound :=
  repair_reference_hierarchy_gt_one (incrementUniformSignedRadius_pos C R)
    C.covectorBound_pos.le hT

/-- A name for the original native Good predicate, canonical kernel
restriction lower bound, and inverse bound, with no altered norm. -/
def RepairReferenceSignedControl (B : SymmetricSquare E →L[ℝ] V)
    (eta : E →L[ℝ] ℝ) (margin : ℝ) : Prop :=
  LinearSecondFormGoodCovector B.toLinearMap eta.toLinearMap ∧
  (∀ z, margin*‖z‖ ≤ ‖covectorRestriction B eta z‖) ∧
  ∃ e : SymmetricSquare eta.ker ≃L[ℝ]
      LinearMap.range (covectorRestriction B eta).toLinearMap,
    (∀ z, (e z).val=covectorRestriction B eta z) ∧
    ‖e.symm.toContinuousLinearMap‖ ≤ margin⁻¹

/-- Both literal cross-host signed covectors have the SAME numerical
moving-kernel margin.  The inputs are only the original transition bound,
operator bound, and membership in the fixed template's operator domain. -/
theorem repair_reference_signed_foreign_control
    (C : UniformActualGoodDictionaryCover K) (R transitionBound : ℝ)
    (hT : 0 ≤ transitionBound)
    (B : SymmetricSquare E →L[ℝ] V) (hB : ‖B‖ ≤ R)
    (dominant : C.indices) (hdom : B ∈ (C.template dominant).operatorDomain)
    (a : EdgePair (Module.finrank ℝ E+1))
    (foreign : C.indices) (b : EdgePair (Module.finrank ℝ E+1))
    (transition : E →L[ℝ] E) (htransition : ‖transition‖ ≤ transitionBound)
    {i j : ℕ} (hij : i < j) :
    let w := repairReferenceSignedHierarchy C R transitionBound
    RepairReferenceSignedControl B
      (w^j • (C.template dominant).covectors a+
        w^i • ((C.template foreign).covectors b).comp transition)
      (incrementUniformSignedMargin C R) ∧
    RepairReferenceSignedControl B
      (w^j • (C.template dominant).covectors a-
        w^i • ((C.template foreign).covectors b).comp transition)
      (incrementUniformSignedMargin C R) := by
  intro w
  have hw0 : 0 < w := zero_lt_one.trans
    (repairReferenceSignedHierarchy_gt_one C R transitionBound hT)
  have hforeign : ‖((C.template foreign).covectors b).comp transition‖ ≤
      C.covectorBound*transitionBound :=
    (((C.template foreign).covectors b).opNorm_comp_le transition).trans
      (mul_le_mul ((C.bounds foreign).2.2.2.2 b) htransition
        (norm_nonneg transition) C.covectorBound_pos.le)
  have hclose := repair_reference_hierarchy_normalized_close
    (incrementUniformSignedRadius_pos C R) (mul_nonneg C.covectorBound_pos.le hT)
    (((C.template foreign).covectors b).comp transition)
    ((C.template dominant).covectors a) hforeign hij
  exact ⟨increment_uniform_signed_control C R B hB dominant hdom a _ (w^j)
      (pow_ne_zero _ hw0.ne') hclose.1,
    increment_uniform_signed_control C R B hB dominant hdom a _ (w^j)
      (pow_ne_zero _ hw0.ne') hclose.2⟩

/-- Bounded labels give a weight cap before any primary count is known.
This cap pays the actual square-root reserve after reweighting. -/
theorem repair_reference_signed_weight_cap
    (C : UniformActualGoodDictionaryCover K) (R transitionBound : ℝ)
    (hT : 0 ≤ transitionBound) (labelBound : ℕ) {label : ℕ} (hlabel : label ≤ labelBound) :
    0 < repairReferenceSignedHierarchy C R transitionBound ^ label ∧
    repairReferenceSignedHierarchy C R transitionBound ^ label ≤
      repairReferenceSignedHierarchy C R transitionBound ^ labelBound := by
  have hw := repairReferenceSignedHierarchy_gt_one C R transitionBound hT
  exact ⟨pow_pos (zero_lt_one.trans hw) _,pow_le_pow_right₀ hw.le hlabel⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_hierarchy_normalized_close
#print axioms GlobalEmbedding.Continuation.repair_reference_signed_foreign_control
#print axioms GlobalEmbedding.Continuation.repair_reference_signed_weight_cap
