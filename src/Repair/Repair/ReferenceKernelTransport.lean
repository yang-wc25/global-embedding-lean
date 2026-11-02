import GlobalEmbedding.Paper.SymmetricSquareTransportLowerBound
import GlobalEmbedding.Paper.SymmetricSquareMapComposition
import GlobalEmbedding.Paper.SymmetricSquareMapLEval
import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates

/-!
# The original kernel reserve under the actual coordinate differential

The literal kernel of the pulled-back covector is mapped by the genuine
coordinate linear equivalence to the owner's literal kernel.  Its inverse
norm is at most that of the coordinate inverse.  Thus the original
Sym² quotient restriction reserve loses precisely the square of the
inverse-coordinate bound.  Nonzero phase weights leave this kernel and
its canonical norm unchanged.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped TensorProduct Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance referenceKernelRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance referenceKernelSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

def repairReferenceKernelMap (A : E ≃L[ℝ] E) (xi : E →L[ℝ] ℝ) :
    (xi.comp A.toContinuousLinearMap).ker →L[ℝ] xi.ker :=
  (A.toContinuousLinearMap.comp (xi.comp A.toContinuousLinearMap).ker.subtypeL).codRestrict
    xi.ker (fun v => v.property)

def repairReferenceKernelInverse (A : E ≃L[ℝ] E) (xi : E →L[ℝ] ℝ) :
    xi.ker →L[ℝ] (xi.comp A.toContinuousLinearMap).ker :=
  (A.symm.toContinuousLinearMap.comp xi.ker.subtypeL).codRestrict
    (xi.comp A.toContinuousLinearMap).ker (by
      intro v
      change xi (A (A.symm v))=0
      rw [A.apply_symm_apply]
      exact v.property)

def repairReferenceKernelEquiv (A : E ≃L[ℝ] E) (xi : E →L[ℝ] ℝ) :
    (xi.comp A.toContinuousLinearMap).ker ≃L[ℝ] xi.ker :=
  ContinuousLinearEquiv.equivOfInverse (repairReferenceKernelMap A xi)
    (repairReferenceKernelInverse A xi)
    (by intro v; apply Subtype.ext; exact A.symm_apply_apply v)
    (by intro v; apply Subtype.ext; exact A.apply_symm_apply v)

theorem repair_reference_kernel_equiv_inverse_norm (A : E ≃L[ℝ] E) (xi : E →L[ℝ] ℝ) :
    ‖(repairReferenceKernelEquiv A xi).symm.toContinuousLinearMap‖ ≤
      ‖A.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖A.symm v‖ ≤ ‖A.symm.toContinuousLinearMap‖*‖v‖
  exact A.symm.toContinuousLinearMap.le_opNorm v

theorem repair_reference_restriction_transport
    (A : E ≃L[ℝ] E) (xi : E →L[ℝ] ℝ) (B : SymmetricSquare E →L[ℝ] V)
    (z : SymmetricSquare (xi.comp A.toContinuousLinearMap).ker) :
    covectorRestriction (B.comp (symmetricSquareMapL A.toContinuousLinearMap))
      (xi.comp A.toContinuousLinearMap) z =
    covectorRestriction B xi
      (symmetricSquareMap (repairReferenceKernelEquiv A xi).toContinuousLinearMap z) := by
  simp only [covectorRestriction,ContinuousLinearMap.comp_apply,symmetricSquareMapL_apply]
  rw [symmetricSquareMap_comp,symmetricSquareMap_comp]
  rfl

theorem repair_reference_kernel_lower_transport
    (A : E ≃L[ℝ] E) (xi : E →L[ℝ] ℝ) (B : SymmetricSquare E →L[ℝ] V)
    (mu T : ℝ) (hmu : 0 ≤ mu) (hT : 0 < T)
    (hInverse : ‖A.symm.toContinuousLinearMap‖ ≤ T)
    (hLower : ∀ z, mu*‖z‖ ≤ ‖covectorRestriction B xi z‖) :
    ∀ z, (mu/T^2)*‖z‖ ≤
      ‖covectorRestriction (B.comp (symmetricSquareMapL A.toContinuousLinearMap))
        (xi.comp A.toContinuousLinearMap) z‖ := by
  intro z
  rw [repair_reference_restriction_transport]
  apply symmetricSquare_transport_lower_bound (repairReferenceKernelEquiv A xi)
    (covectorRestriction B xi).toLinearMap mu (T^2) hmu (sq_pos_of_pos hT) _ hLower z
  exact (sq_le_sq₀ (norm_nonneg _) hT.le).mpr
    ((repair_reference_kernel_equiv_inverse_norm A xi).trans hInverse)

/-- This is the required numerical reference reserve in an arbitrary
observing host, for any nonzero actual phase weight. -/
theorem repair_reference_weighted_template_kernel_transport
    [FiniteDimensional ℝ V]
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (i : C.indices)
    (a : EdgePair (Module.finrank ℝ E+1))
    (B : SymmetricSquare E →L[ℝ] V) (hB : B ∈ (C.template i).operatorDomain)
    (A : E ≃L[ℝ] E) (T : ℝ) (hT : 0 < T)
    (hInverse : ‖A.symm.toContinuousLinearMap‖ ≤ T)
    (weight : ℝ) (hweight : weight ≠ 0) :
    ∀ z, (C.restrictionReserve/T^2)*‖z‖ ≤
      ‖covectorRestriction (B.comp (symmetricSquareMapL A.toContinuousLinearMap))
        (weight • ((C.template i).covectors a).comp A.toContinuousLinearMap) z‖ := by
  let xi := ((C.template i).covectors a).comp A.toContinuousLinearMap
  have hLower : ∀ z, (C.restrictionReserve/T^2)*‖z‖ ≤
      ‖covectorRestriction (B.comp (symmetricSquareMapL A.toContinuousLinearMap)) xi z‖ := by
    apply repair_reference_kernel_lower_transport A ((C.template i).covectors a) B
      C.restrictionReserve T C.restrictionReserve_pos.le hT hInverse
    intro z
    exact (mul_le_mul_of_nonneg_right (C.bounds i).1 (norm_nonneg z)).trans
      (((C.template i).operator_control B hB a).2.1 z)
  have hker : (weight • xi).ker = xi.ker := by
    change LinearMap.ker (weight • xi.toLinearMap) = LinearMap.ker xi.toLinearMap
    exact LinearMap.ker_smul xi.toLinearMap weight hweight
  let bound (S : Submodule ℝ E) : Prop :=
    ∀ z : SymmetricSquare S, (C.restrictionReserve/T^2)*‖z‖ ≤
      ‖(B.comp (symmetricSquareMapL A.toContinuousLinearMap)) (symmetricSquareMapL S.subtypeL z)‖
  change bound (weight • xi).ker
  rw [hker]
  exact hLower

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_kernel_lower_transport
#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_template_kernel_transport
