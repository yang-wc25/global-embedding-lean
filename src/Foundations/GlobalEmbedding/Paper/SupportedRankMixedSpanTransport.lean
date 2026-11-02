import GlobalEmbedding.Paper.SupportedRankSymmetricSquareSplitting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Transport to the actual mixed symmetric-square range

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1007–1008 and 1020–1027. Reuse the accepted splitting on the ORIGINAL binary
quotient. No raw t-span proof, self-adjoint carrier or norm is reconstructed.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {U V K : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup K] [Module ℝ K]

/-- The original splitting followed by the actual injective mixed-product range equivalence.
Source: `prop:supported-rank`, `Z=e⊙V` in the original symmetric square. -/
def supportedRankMixedRangeEquiv (d : (U × ℝ) ≃ₗ[ℝ] V) :
    (U × ℝ) ≃ₗ[ℝ]
      LinearMap.range (symmetricSquareProduct V (supportedRankSplitVector d)) :=
  d.trans (LinearEquiv.ofInjective
    (symmetricSquareProduct V (supportedRankSplitVector d))
    (supported_rank_symmetric_square_splitting d).2.1)

/-- After inclusion, the actual mixed-range equivalence is precisely `e⊙d(u,t)`.
Source: `prop:supported-rank`, the literal mixed product; normalization is unchanged. -/
@[simp] theorem supportedRankMixedRangeEquiv_apply (d : (U × ℝ) ≃ₗ[ℝ] V) (p : U × ℝ) :
    (supportedRankMixedRangeEquiv d p : SymmetricSquare V) =
      symmetricSquareProduct V (supportedRankSplitVector d) (d p) := rfl

/-- Postcomposition with the actual mixed-range equivalence gives the genuine Hom equivalence.
Source: `prop:supported-rank`, transport from `Hom(K,U⊕ℝe)` to `Hom(K,Z)`. -/
def supportedRankMixedHomEquiv (d : (U × ℝ) ≃ₗ[ℝ] V) :
    (K →ₗ[ℝ] U × ℝ) ≃ₗ[ℝ]
      K →ₗ[ℝ] LinearMap.range (symmetricSquareProduct V (supportedRankSplitVector d)) :=
  (LinearEquiv.refl ℝ K).arrowCongr (supportedRankMixedRangeEquiv d)

/-- The transported lifted column has the SAME evaluation coefficient and actual mixed vector.
Proof: postcomposition commutes with the literal scalar multiplication.
Source: `prop:supported-rank`, the maps `Q↦ξ Q(z,z)` in `Z`. -/
theorem supportedRankMixedHomEquiv_rankOne (d : (U × ℝ) ≃ₗ[ℝ] V)
    (a : Module.Dual ℝ K) (p : U × ℝ) :
    supportedRankMixedHomEquiv (K := K) d (a.smulRight p) =
      a.smulRight (supportedRankMixedRangeEquiv d p) := by
  ext k
  simp [supportedRankMixedHomEquiv, LinearEquiv.arrowCongr_apply]

/-- The actual mixed-column span has exactly the dimension of the literal lifted span.

Proof: identify the two SAME-coefficient families under the genuine Hom equivalence,
then use native span image and preservation of submodule dimension. No raw span
bound or evaluation-span identity is assumed or reproved here.
Source: `prop:supported-rank`, fixed mixed-summand transport before positive compression. -/
theorem supportedRank_mixed_span_finrank [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ K] (d : (U × ℝ) ≃ₗ[ℝ] V)
    (a : U → Module.Dual ℝ K) (Ω : Set U) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun p : Ω × ℝ ↦
      (a p.1).smulRight (supportedRankMixedRangeEquiv d ((p.1 : U), p.2)))) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun p : Ω × ℝ ↦
        (a p.1).smulRight ((p.1 : U), p.2))) := by
  let L := Submodule.span ℝ (Set.range fun p : Ω × ℝ ↦
    (a p.1).smulRight ((p.1 : U), p.2))
  let e := supportedRankMixedHomEquiv (K := K) d
  have hmap : L.map e.toLinearMap = Submodule.span ℝ (Set.range fun p : Ω × ℝ ↦
      (a p.1).smulRight (supportedRankMixedRangeEquiv d ((p.1 : U), p.2))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext p
    exact supportedRankMixedHomEquiv_rankOne d (a p.1) ((p.1 : U), p.2)
  rw [← hmap]
  exact e.finrank_map_eq L

#print axioms supportedRankMixedRangeEquiv
#print axioms supportedRankMixedRangeEquiv_apply
#print axioms supportedRankMixedHomEquiv
#print axioms supportedRankMixedHomEquiv_rankOne
#print axioms supportedRank_mixed_span_finrank

end GlobalEmbedding.Paper
