import GlobalEmbedding.Paper.SymmetricSquareOperatorSupport
import GlobalEmbedding.Paper.SymmetricSquareHilbertPairing
import GlobalEmbedding.Paper.SymmetricSquareCovectorEvaluation

/-!
# Actual mixed orthogonality and quadratic evaluation from original support

Source: original `prop:supported-rank`, lines 1007–1022, especially equation (9.4).
DAG: `supported-rank-mixed-orthogonality`. Exclusive worker W2.
All objects, norms and the native closed-quotient inner product are unchanged.
-/

noncomputable section
open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

local instance mixedOrthogonalSquareRelationsClosed :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

local instance mixedOrthogonalSquareNormed : NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

local instance mixedOrthogonalSquareInner : InnerProductSpace ℝ (SymmetricSquare V) :=
  { Submodule.instQuotientInnerProductSpace (symmetricSquareRelations V) with
    toNormedSpace := squareNS V }

/-- Original support makes each literal mixed product genuinely perpendicular to K.
Source: `Z=e⊙V⊂K⊥` in the original kernel-variation computation. -/
theorem symmetricSquare_mixed_mem_orthogonal (U : Submodule ℝ V)
    (K : Submodule ℝ (SymmetricSquare V))
    (hK : K ≤ LinearMap.range (symmetricSquareLinearMap U.subtype))
    (e : V) (he : e ∈ Uᗮ) (v : V) :
    symmetricSquareProduct V e v ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro q hq
  rw [symmetricSquare_inner_product_eq_operator]
  have hr := (symmetricSquare_mem_range_iff_operator_range U q).mp (hK hq)
  have hz := quadraticSpace_kills_orthogonal (symmetricSquareToSelfAdjoint q).val
    (symmetricSquareToSelfAdjoint q).property.isSymmetric U hr he
  rw [hz, inner_zero_left]

/-- The SAME actual mixed range is contained in the original K orthogonal complement.
Source: original positive-compression domain `Z⊂K⊥`. -/
theorem symmetricSquare_mixed_range_le_orthogonal (U : Submodule ℝ V)
    (K : Submodule ℝ (SymmetricSquare V))
    (hK : K ≤ LinearMap.range (symmetricSquareLinearMap U.subtype))
    (e : V) (he : e ∈ Uᗮ) :
    LinearMap.range (symmetricSquareProduct V e) ≤ Kᗮ := by
  rintro _ ⟨v, rfl⟩
  exact symmetricSquare_mixed_mem_orthogonal U K hK e he v

/-- Actual ξ² is pairing with the actual diagonal product in the original norm.
Source: literal `Q(z,z)` in original equation (9.4). -/
theorem supportedRankCovectorSquare_eq_quotient_inner (q : SymmetricSquare V) (x : V) :
    supportedRankCovectorSquare (innerₗ V x) q =
      inner ℝ q (symmetricSquareProduct V x x) := by
  rw [supportedRankCovectorSquare_inner_eq_operator, symmetricSquare_inner_product_eq_operator]

/-- For the SAME supported q, the actual square at z+t e is exactly its square at z.
Source: original legal covectors ξ=z+t e and equation (9.4). -/
theorem supportedRankCovectorSquare_add_orthogonal (U : Submodule ℝ V)
    (q : SymmetricSquare V)
    (hq : q ∈ LinearMap.range (symmetricSquareLinearMap U.subtype))
    (e : V) (he : e ∈ Uᗮ) (z : V) (t : ℝ) :
    supportedRankCovectorSquare (innerₗ V (z + t • e)) q =
      supportedRankCovectorSquare (innerₗ V z) q := by
  rw [supportedRankCovectorSquare_inner_eq_operator, supportedRankCovectorSquare_inner_eq_operator]
  have hr := (symmetricSquare_mem_range_iff_operator_range U q).mp hq
  have hz := quadraticSpace_kills_orthogonal (symmetricSquareToSelfAdjoint q).val
    (symmetricSquareToSelfAdjoint q).property.isSymmetric U hr he
  have hc : inner ℝ ((symmetricSquareToSelfAdjoint q).val z) e = 0 := by
    calc
      _ = inner ℝ z ((symmetricSquareToSelfAdjoint q).val e) :=
        (symmetricSquareToSelfAdjoint q).property.isSymmetric z e
      _ = 0 := by rw [hz, inner_zero_right]
  simp only [map_add, map_smul, hz, smul_zero, add_zero, inner_add_right,
    real_inner_smul_right, hc, mul_zero]

end GlobalEmbedding.Paper
