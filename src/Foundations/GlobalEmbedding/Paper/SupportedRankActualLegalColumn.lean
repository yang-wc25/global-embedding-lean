import GlobalEmbedding.Paper.SymmetricSquareHilbertPairing
import GlobalEmbedding.Paper.ContractionKernelDictionary
import GlobalEmbedding.Paper.SupportedRankKernelGraphVariation
import GlobalEmbedding.Paper.SupportedRankLegalVariation

/-!
# The actual original legal normal and its actual kernel derivative

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1014–1022, equation (9.4). The vector is defined from the genuine restricted
adjoint inverse and proved legal using the SAME original quotient Hilbert pairing.
-/

noncomputable section
open scoped TensorProduct

namespace GlobalEmbedding.Paper

private local instance actualSquareRelationsClosed {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance actualSquareNormed {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

private noncomputable local instance actualSquareSpace {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : NormedSpace ℝ (SymmetricSquare V) :=
  (inferInstance : InnerProductSpace ℝ (SymmetricSquare V)).toNormedSpace

private noncomputable local instance actualSquareModule {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : Module ℝ (SymmetricSquare V) :=
  (actualSquareSpace (V := V)).toModule

private noncomputable local instance actualSquareAddMonoid {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : AddCommMonoid (SymmetricSquare V) :=
  (actualSquareNormed (V := V)).toAddCommMonoid

private noncomputable local instance actualSquareTopology {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : TopologicalSpace (SymmetricSquare V) :=
  (actualSquareNormed (V := V)).toUniformSpace.toTopologicalSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The original normal `ν` is obtained by solving the actual restricted adjoint equation.
The mixed-perpendicular proof is later supplied by the actual supported-kernel dictionary.
No desired normal, inverse, derivative or legality conclusion is supplied as data.
Source: `prop:supported-rank`, `B*νξ=e⊙ξ`. -/
def supportedRankActualLegalVector (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (e x : V)
    (hm : symmetricSquareProduct V e x ∈ B.kerᗮ) : W :=
  (supportedRankKernelAdjointEquiv B hB).symm ⟨symmetricSquareProduct V e x, hm⟩

/-- The constructed normal solves the literal original adjoint equation.
Proof: apply the already proved actual restricted-adjoint inverse identity.
Source: `prop:supported-rank`, the equation defining the legal normal. -/
theorem supportedRankActualLegalVector_adjoint (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (e x : V)
    (hm : symmetricSquareProduct V e x ∈ B.kerᗮ) :
    B.adjoint (supportedRankActualLegalVector B hB e x hm) = symmetricSquareProduct V e x :=
  supportedRankKernelAdjointEquiv_symm_spec B hB ⟨symmetricSquareProduct V e x, hm⟩

/-- The constructed original vector belongs to the literal `Eξ` for `ξ=⟨x,-⟩`.

Proof: pair with every actual `B(Sym²ker ξ)` value. Actual adjoint duality turns
the pairing into the original quotient product pairing. The accepted same-quotient
dictionary identifies this with contraction at `x`, which vanishes on the literal
symmetric square of `ker ξ`. No legality conclusion is assumed.
Source: `prop:supported-rank`, lines 1014–1017. -/
theorem supportedRankActualLegalVector_mem (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (e x : V)
    (hm : symmetricSquareProduct V e x ∈ B.kerᗮ) :
    supportedRankActualLegalVector B hB e x hm ∈
      supportedRankLegalValueSpace B.toLinearMap (innerₗ V x) := by
  apply (supportedRank_mem_legalValueSpace_iff B.toLinearMap (innerₗ V x) _).mpr
  intro q
  change inner ℝ (B (symmetricSquareLinearMap (innerₗ V x).ker.subtype q))
    (supportedRankActualLegalVector B hB e x hm) = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, supportedRankActualLegalVector_adjoint]
  rw [symmetricSquareProduct_comm V e x, symmetricSquare_inner_product_eq_operator,
    symmetricSquareToSelfAdjoint_apply]
  have hzero : contractionKernelQuotientMap (innerₗ V x)
      (symmetricSquareLinearMap (innerₗ V x).ker.subtype q) = 0 :=
    LinearMap.congr_fun (contractionKernel_comp_inclusion_eq_zero (innerₗ V x)) q
  rw [hzero, inner_zero_left]

/-- The actual legal quotient column has exactly the actual inverse-Gram kernel variation.

Proof: the same quotient rank-one map is the continuous square functional smulRight
the constructed normal. Apply the accepted actual rank-one kernel derivative and
the actual adjoint identity, with its literal mixed tensor in `K⊥`.
Source: `prop:supported-rank`, equation (9.4). -/
theorem supportedRankActualLegalVector_kernel_derivative
    (B : SymmetricSquare V →L[ℝ] W) (hB : Function.Surjective B) (e x : V)
    (hm : symmetricSquareProduct V e x ∈ B.kerᗮ) (q : B.ker) :
    (fderiv ℝ (supportedRankKernelGraph B hB) B)
        (supportedRankLegalVariation (innerₗ V x)
          (supportedRankActualLegalVector B hB e x hm)).toContinuousLinearMap q =
      -(supportedRankCovectorSquare (innerₗ V x) q •
        ((supportedRankKernelComplementMap B).adjoint.comp
          (supportedRankKernelComplementMap B)).inverse
            ⟨symmetricSquareProduct V e x, hm⟩) := by
  let ν := supportedRankActualLegalVector B hB e x hm
  let l := (supportedRankCovectorSquare (innerₗ V x)).toContinuousLinearMap
  have hcolumn : (supportedRankLegalVariation (innerₗ V x) ν).toContinuousLinearMap =
      l.smulRight ν := by
    apply ContinuousLinearMap.ext
    intro p
    rfl
  change (fderiv ℝ (supportedRankKernelGraph B hB) B)
    (supportedRankLegalVariation (innerₗ V x) ν).toContinuousLinearMap q = _
  rw [hcolumn]
  exact supportedRankKernelGraph_fderiv_rankOne_adjoint B hB l ν
    ⟨symmetricSquareProduct V e x, hm⟩
    (supportedRankActualLegalVector_adjoint B hB e x hm) q

#print axioms supportedRankActualLegalVector
#print axioms supportedRankActualLegalVector_adjoint
#print axioms supportedRankActualLegalVector_mem
#print axioms supportedRankActualLegalVector_kernel_derivative
#print axioms actualSquareRelationsClosed
#print axioms actualSquareNormed
#print axioms actualSquareSpace
#print axioms actualSquareModule
#print axioms actualSquareAddMonoid
#print axioms actualSquareTopology

end GlobalEmbedding.Paper
