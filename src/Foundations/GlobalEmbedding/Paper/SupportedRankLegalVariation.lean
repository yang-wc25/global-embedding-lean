import GlobalEmbedding.Paper.SupportedRankCovectorSquareRelations
import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# The original legal rank-one columns on the binary symmetric-square quotient

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:saturation`,
lines 948–953, and `prop:supported-rank`, lines 998–1022.

These definitions use the existing quotient, its existing relation-killing theorem,
and the literal covector kernel. No self-adjoint representation or norm is chosen.
-/

noncomputable section

namespace GlobalEmbedding.Paper

open scoped TensorProduct

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]

/-- The original functional `ξ²` on the actual binary quotient. Its lift is justified
by the accepted relation-killing theorem. Source: `prop:supported-rank`, equation (9.4). -/
def supportedRankCovectorSquare (ξ : V →ₗ[ℝ] ℝ) : SymmetricSquare V →ₗ[ℝ] ℝ :=
  (symmetricSquareRelations V).liftQ (supportedRankCovectorSquareTensorMap ξ)
    (supportedRankCovectorSquare_killsRelations ξ)

/-- On the original symmetric product the square is literal covector multiplication.
Source: `prop:supported-rank`, the evaluation `ξ²(Q)=Q(ξ,ξ)`. -/
@[simp] theorem supportedRankCovectorSquare_product (ξ : V →ₗ[ℝ] ℝ) (v w : V) :
    supportedRankCovectorSquare ξ (symmetricSquareProduct V v w) = ξ v * ξ w := by
  exact supportedRankCovectorSquareTensorMap_tmul ξ v w

/-- The square vanishes on the symmetric square of the actual kernel of `ξ`.

Proof: on each pure product both covector values are zero. Tensor-product
extensionality and surjectivity of the existing quotient map give the assertion.
Source: `prop:saturation`, the literal space `Sym² ker ξ`. -/
theorem supportedRankCovectorSquare_kernel (ξ : V →ₗ[ℝ] ℝ)
    (q : SymmetricSquare ξ.ker) :
    supportedRankCovectorSquare ξ (symmetricSquareLinearMap ξ.ker.subtype q) = 0 := by
  have hcomp : ((supportedRankCovectorSquare ξ).comp
      (symmetricSquareLinearMap ξ.ker.subtype)).comp (symmetricSquareQuotient ξ.ker) = 0 := by
    apply TensorProduct.ext'
    intro v w
    change supportedRankCovectorSquare ξ
      (symmetricSquareLinearMap ξ.ker.subtype (symmetricSquareProduct ξ.ker v w)) = 0
    unfold symmetricSquareLinearMap symmetricBilinearDescend
    change supportedRankCovectorSquare ξ
      (TensorProduct.lift
        (((symmetricSquareProduct V).compl₂ ξ.ker.subtype).comp ξ.ker.subtype)
        (v ⊗ₜ[ℝ] w)) = 0
    rw [TensorProduct.lift.tmul]
    change supportedRankCovectorSquare ξ (symmetricSquareProduct V (v : V) (w : V)) = 0
    rw [supportedRankCovectorSquare_product, v.property, zero_mul]
  induction q using Submodule.Quotient.induction_on with
  | _ t => exact congrArg (fun L : ξ.ker ⊗[ℝ] ξ.ker →ₗ[ℝ] ℝ ↦ L t) hcomp

section LegalColumn

variable [AddCommGroup W] [Module ℝ W]

/-- The original rank-one variation `ν⊗ξ²`, with the actual quotient as domain.
Source: `prop:supported-rank`, lines 999–1001. -/
def supportedRankLegalVariation (ξ : V →ₗ[ℝ] ℝ) (ν : W) :
    SymmetricSquare V →ₗ[ℝ] W :=
  (supportedRankCovectorSquare ξ).smulRight ν

/-- The literal value of the legal rank-one column. Source: `prop:supported-rank`. -/
@[simp] theorem supportedRankLegalVariation_apply (ξ : V →ₗ[ℝ] ℝ) (ν : W)
    (q : SymmetricSquare V) :
    supportedRankLegalVariation ξ ν q = supportedRankCovectorSquare ξ q • ν := rfl

/-- On pure symmetric products the rank-one column has the original normalization.
Source: `prop:supported-rank`, equation (9.4). -/
@[simp] theorem supportedRankLegalVariation_product (ξ : V →ₗ[ℝ] ℝ) (ν : W) (v w : V) :
    supportedRankLegalVariation ξ ν (symmetricSquareProduct V v w) = (ξ v * ξ w) • ν := by
  rw [supportedRankLegalVariation_apply, supportedRankCovectorSquare_product]

/-- Legal columns vanish on `Sym² ker ξ`; this follows from the actual square functional.
Source: `prop:supported-rank`, the legal covector restriction. -/
theorem supportedRankLegalVariation_kernel (ξ : V →ₗ[ℝ] ℝ) (ν : W)
    (q : SymmetricSquare ξ.ker) :
    supportedRankLegalVariation ξ ν (symmetricSquareLinearMap ξ.ker.subtype q) = 0 := by
  rw [supportedRankLegalVariation_apply, supportedRankCovectorSquare_kernel, zero_smul]

end LegalColumn

section LegalValue

variable [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The literal original `Eξ=(B(Sym² ker ξ))⊥`. No chosen basis, good covector,
surjectivity or desired normal-rank conclusion is built into this definition.
Source: `prop:saturation`, lines 948–953. -/
def supportedRankLegalValueSpace (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →ₗ[ℝ] ℝ) :
    Submodule ℝ W :=
  (LinearMap.range (B.comp (symmetricSquareLinearMap ξ.ker.subtype)))ᗮ

/-- Membership in `Eξ` is exactly annihilation of all literal restricted values.
Proof: unfold range membership in the native orthogonal-complement criterion.
Source: `prop:saturation`, definition of `Eξ`. -/
theorem supportedRank_mem_legalValueSpace_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →ₗ[ℝ] ℝ) (ν : W) :
    ν ∈ supportedRankLegalValueSpace B ξ ↔
      ∀ q : SymmetricSquare ξ.ker,
        inner ℝ (B (symmetricSquareLinearMap ξ.ker.subtype q)) ν = 0 := by
  constructor
  · intro hν q
    exact (Submodule.mem_orthogonal _ _).mp hν _ ⟨q, rfl⟩
  · intro hν
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨q, rfl⟩
    exact hν q

/-- Every value of a legal column with `ν∈Eξ` still lies in the same actual `Eξ`.
Proof: a linear subspace is closed under the literal scalar multiple defining the column.
Source: `prop:supported-rank`, legal variation `ν⊗ξ²`. -/
theorem supportedRankLegalVariation_mem_valueSpace
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →ₗ[ℝ] ℝ)
    (ν : W) (hν : ν ∈ supportedRankLegalValueSpace B ξ) (q : SymmetricSquare V) :
    supportedRankLegalVariation ξ ν q ∈ supportedRankLegalValueSpace B ξ :=
  (supportedRankLegalValueSpace B ξ).smul_mem _ hν

end LegalValue

#print axioms supportedRankCovectorSquare
#print axioms supportedRankCovectorSquare_product
#print axioms supportedRankCovectorSquare_kernel
#print axioms supportedRankLegalVariation
#print axioms supportedRankLegalVariation_apply
#print axioms supportedRankLegalVariation_product
#print axioms supportedRankLegalVariation_kernel
#print axioms supportedRankLegalValueSpace
#print axioms supportedRank_mem_legalValueSpace_iff
#print axioms supportedRankLegalVariation_mem_valueSpace

end GlobalEmbedding.Paper
