import GlobalEmbedding.Paper.SupportedLocusLocalEquations
import GlobalEmbedding.Paper.SymmetricSquareLinearMapEquality
import GlobalEmbedding.Paper.SymmetricSquareMapInverse
import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Literal supported kernels in actual source and normal coordinates

Source: `thm:upgrade`, supported-incidence operations. An orthogonal normal
identification only postcomposes the true second form by an injective map;
a source frame precomposes it by the canonical binary symmetric-square map.
The statements below prove that these operations preserve the ORIGINAL
`HasSupportedKernel` predicate. Thus zeroes of its actual supported chart
remain actual geometric incidences after both coordinate changes.
-/

noncomputable section
open Module Set
open scoped TensorProduct
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section Algebraic
variable {V V' W W' : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']

/-- The actual normal-space identification cannot change the supported kernel.
Only injectivity is required; no orientation or isometry is used. -/
theorem hasSupportedKernel_postcomp_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (j : W →ₗ[ℝ] W')
    (hj : Function.Injective j) :
    HasSupportedKernel (j.comp B) ↔ HasSupportedKernel B := by
  have hker : (j.comp B).ker = B.ker := by
    ext q
    change j (B q) = 0 ↔ B q = 0
    constructor
    · intro h
      exact hj (h.trans j.map_zero.symm)
    · intro h
      rw [h, map_zero]
  unfold HasSupportedKernel
  rw [hker]

/-- Evaluation of the existing canonical square map on an original product. -/
private theorem supportedCoordinates_square_product
    (g : V →ₗ[ℝ] V') (v w : V) :
    symmetricSquareLinearMap g (symmetricSquareProduct V v w) =
      symmetricSquareProduct V' (g v) (g w) :=
  symmetricBilinearDescend_product (((symmetricSquareProduct V').compl₂ g).comp g)
    (fun v w ↦ symmetricSquareProduct_comm V' (g v) (g w)) v w

/-- The same canonical symmetric-square map carries tensors supported on U
into tensors supported on its actual image under a linear coordinate map.
The proof uses the existing quotient-product characterization, not a new
symmetric-square model or support predicate. -/
theorem symmetricSquareLinearMap_mem_image_support
    (f : V →ₗ[ℝ] V') (U : Submodule ℝ V) {Q : SymmetricSquare V}
    (hQ : Q ∈ (symmetricSquareLinearMap U.subtype).range) :
    symmetricSquareLinearMap f Q ∈
      (symmetricSquareLinearMap (U.map f).subtype).range := by
  let fU : U →ₗ[ℝ] U.map f :=
    (f.comp U.subtype).codRestrict _ (fun u ↦ ⟨u, u.property, rfl⟩)
  have hnatural : (symmetricSquareLinearMap f).comp (symmetricSquareLinearMap U.subtype) =
      (symmetricSquareLinearMap (U.map f).subtype).comp (symmetricSquareLinearMap fU) := by
    apply (symmetricSquareRelations U).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change symmetricSquareLinearMap f
        (symmetricSquareLinearMap U.subtype (symmetricSquareProduct U v w)) =
      symmetricSquareLinearMap (U.map f).subtype
        (symmetricSquareLinearMap fU (symmetricSquareProduct U v w))
    rw [supportedCoordinates_square_product, supportedCoordinates_square_product,
      supportedCoordinates_square_product, supportedCoordinates_square_product]
    rfl
  obtain ⟨q, rfl⟩ := hQ
  refine ⟨symmetricSquareLinearMap fU q, ?_⟩
  exact (congrArg (fun L : SymmetricSquare U →ₗ[ℝ] SymmetricSquare V' ↦ L q) hnatural).symm

end Algebraic

section SourceCoordinates
variable {V V' W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [AddCommGroup W] [Module ℝ W]

/-- If the coordinate form is supported, its actual underlying second form
is supported on the image hyperplane. This uses the original square functor. -/
theorem hasSupportedKernel_of_source_coordinates
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : V' ≃L[ℝ] V)
    (h : HasSupportedKernel (B.comp (symmetricSquareLinearMap e.toLinearMap))) :
    HasSupportedKernel B := by
  obtain ⟨U, hU, hK⟩ := h
  refine ⟨U.map e.toLinearMap, ?_, ?_⟩
  · rw [e.toLinearEquiv.finrank_map_eq, ← e.finrank_eq]
    exact hU
  · intro Q hQ
    have hinv : symmetricSquareLinearMap e.toLinearMap
        (symmetricSquareLinearMap e.symm.toLinearMap Q) = Q := by
      have he : symmetricSquareLinearMap e.toLinearMap =
          symmetricSquareMap e.toContinuousLinearMap :=
        symmetric_square_linear_map_eq e.toContinuousLinearMap
      have he' : symmetricSquareLinearMap e.symm.toLinearMap =
          symmetricSquareMap e.symm.toContinuousLinearMap :=
        symmetric_square_linear_map_eq e.symm.toContinuousLinearMap
      rw [he, he']
      exact symmetricSquareMap_symm e.symm Q
    have hQ' : symmetricSquareLinearMap e.symm.toLinearMap Q ∈
        (B.comp (symmetricSquareLinearMap e.toLinearMap)).ker := by
      change B (symmetricSquareLinearMap e.toLinearMap
        (symmetricSquareLinearMap e.symm.toLinearMap Q)) = 0
      rw [hinv]
      exact hQ
    simpa only [hinv] using
      symmetricSquareLinearMap_mem_image_support e.toLinearMap U (hK hQ')

/-- A true invertible source frame preserves the original supported-kernel
condition. The actual support hyperplane is transported by that frame, with
its exact codimension retained. -/
theorem hasSupportedKernel_source_coordinates_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : V' ≃L[ℝ] V) :
    HasSupportedKernel (B.comp (symmetricSquareLinearMap e.toLinearMap)) ↔
      HasSupportedKernel B := by
  constructor
  · exact hasSupportedKernel_of_source_coordinates B e
  · intro h
    apply hasSupportedKernel_of_source_coordinates
      (B.comp (symmetricSquareLinearMap e.toLinearMap)) e.symm
    have hfun : (B.comp (symmetricSquareLinearMap e.toLinearMap)).comp
        (symmetricSquareLinearMap e.symm.toLinearMap) = B := by
      apply LinearMap.ext
      intro Q
      change B (symmetricSquareLinearMap e.toLinearMap
        (symmetricSquareLinearMap e.symm.toLinearMap Q)) = B Q
      have he : symmetricSquareLinearMap e.toLinearMap =
          symmetricSquareMap e.toContinuousLinearMap :=
        symmetric_square_linear_map_eq e.toContinuousLinearMap
      have he' : symmetricSquareLinearMap e.symm.toLinearMap =
          symmetricSquareMap e.symm.toContinuousLinearMap :=
        symmetric_square_linear_map_eq e.symm.toContinuousLinearMap
      rw [he, he']
      exact congrArg B (symmetricSquareMap_symm e.symm Q)
    rw [hfun]
    exact h

end SourceCoordinates

section ActualIncidence
variable {E V W Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- The zero set of the actual supported chart in identified normal/source
coordinates is exactly the ORIGINAL supported-kernel condition of B. The
coordinate dictionary `hC` is a literal equality of second-form operators,
not an assumed equivalence of predicates or an incidence-rank hypothesis. -/
theorem supported_equation_zero_iff_original_coordinates
    (B0 : SymmetricSquare E →L[ℝ] Z)
    (chart : SupportedLocusLocalEquations
      {C : SymmetricSquare E →L[ℝ] Z |
        Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
      {C : SymmetricSquare E →L[ℝ] Z | HasSupportedKernel C.toLinearMap} B0)
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : E ≃L[ℝ] V)
    (j : W →ₗ[ℝ] Z) (hj : Function.Injective j)
    (C : SymmetricSquare E →L[ℝ] Z)
    (hC : C.toLinearMap = j.comp (B.comp (symmetricSquareLinearMap e.toLinearMap)))
    (hdom : C ∈ chart.domain) :
    chart.equation C = 0 ↔ HasSupportedKernel B := by
  rw [← chart.mem_locus_iff C hdom]
  change HasSupportedKernel C.toLinearMap ↔ HasSupportedKernel B
  rw [hC, hasSupportedKernel_postcomp_iff _ j hj,
    hasSupportedKernel_source_coordinates_iff B e]

/-- For dimension-three joint removal, the exact incidence is supportedness
at the first endpoint AND equality of the two actual values. This equivalence
never replaces it by the stronger condition of eliminating supported kernels. -/
theorem supported_coincidence_zero_iff_original_coordinates
    (B0 : SymmetricSquare E →L[ℝ] Z)
    (chart : SupportedLocusLocalEquations
      {C : SymmetricSquare E →L[ℝ] Z |
        Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
      {C : SymmetricSquare E →L[ℝ] Z | HasSupportedKernel C.toLinearMap} B0)
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : E ≃L[ℝ] V)
    (j : W →ₗ[ℝ] Z) (hj : Function.Injective j)
    (C : SymmetricSquare E →L[ℝ] Z)
    (hC : C.toLinearMap = j.comp (B.comp (symmetricSquareLinearMap e.toLinearMap)))
    (hdom : C ∈ chart.domain)
    {Y : Type*} [AddCommGroup Y] (Fx Fy : Y) :
    (chart.equation C, Fx - Fy) = 0 ↔ HasSupportedKernel B ∧ Fx = Fy := by
  rw [Prod.mk.injEq]
  simp only [Prod.fst_zero, Prod.snd_zero, sub_eq_zero,
    supported_equation_zero_iff_original_coordinates B0 chart B e j hj C hC hdom]

end ActualIncidence

#print axioms hasSupportedKernel_postcomp_iff
#print axioms symmetricSquareLinearMap_mem_image_support
#print axioms hasSupportedKernel_of_source_coordinates
#print axioms hasSupportedKernel_source_coordinates_iff
#print axioms supported_equation_zero_iff_original_coordinates
#print axioms supported_coincidence_zero_iff_original_coordinates

end GlobalEmbedding.Upgrade
