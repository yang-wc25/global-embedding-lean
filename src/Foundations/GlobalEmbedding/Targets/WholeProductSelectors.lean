import GlobalEmbedding.Paper.WholeProductSelectorFromCollar
import GlobalEmbedding.Paper.LeastSingularNormBound
import GlobalEmbedding.Paper.SymmetricSquareNontrivial
import GlobalEmbedding.Targets.AnalyticCollar

/-!
# The full original whole-product selector

Source: `literature/parallelizable-stable-plus-one/main.tex`, cor:selector, lines565–584.
DAG: cor-selector. Exclusive worker W3. Full original statement for ROOT independent review.
The proof supplies the actual original collar internally, with no extra premise.
ROOT reviewed the full statement and authorized normal import of the proved original collar.
The same canonical tensor quotient norms are used in the independent reference.
-/

noncomputable section

open Manifold
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

local instance wholeProductSelectorSquareRelationsClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

noncomputable local instance wholeProductSelectorSquareNormed
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- For every original n=m+1>=2 and every C_i>=2, one smooth map on the entire
original Hopf product into exactly R^(s_n+1) has partial Gram I. Its true partial
second form is injective on the whole binary symmetric square of the old generator
span and has one positive uniform minimum singular value in the canonical tensor
quotient norm. The true partial normal is the complement of span{Y_i S}, realized
by the same genuine multi-orbit leaf; it is not the total normal of the Hopf product.

Every coordinate-subsphere restriction is literally this one S precomposed with
the actual coordinate inclusion. All positive smaller dimensions and all coordinate
injections are included. The restrictions retain the same epsilon and true operator,
without choosing a new map or margin. The n=m+1 parameterization covers all n>=2.

Proof: apply the original collar theorem to the first m factors; its actual target
dimension s_m+m+1 is exactly the one used by the accepted same-collar selector.
The latter internally chooses an actual planar selector and one power K and returns
one S with full Gram I, true old symmetric-square injectivity and a uniform norm
bound. Original m>=1 makes the old symmetric square nontrivial. The already proved
least-singular-norm characterization converts this very bound to the stated actual
minimum. The already proved whole-operator equality on literal coordinate inclusions
transfers all conclusions with the same epsilon. No analytic collar, desired selector,
rank, metric identity, positive margin or restriction compatibility is an input.

Source: cor:selector, statement565–572 and proof574–584; prop:collar. -/
theorem whole_product_hopf_selector (m : ℕ) (hm : 1 ≤ m)
    (C : Fin (m + 1) → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have h := hC i; omega⟩
    ∃ S : FreeHopfProduct C → EuclideanSpace ℝ (Fin (closedAmbientDimension (m + 1))),
    ∃ hS : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (closedAmbientDimension (m + 1)))) ∞ S,
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S x) = 1) ∧
      (∀ x, Function.Injective (selectorOldSecondForm C S hS x)) ∧
      (∀ x v, ε * ‖v‖ ≤ ‖selectorOldSecondForm C S hS x v‖) ∧
      (∀ x, ε ≤ leastSingularNorm
        (selectorOldSecondForm C S hS x).toContinuousLinearMap) ∧
      ∀ (smallC : Fin (m + 1) → ℕ) (hsmall : ∀ i, 0 < smallC i)
        (e : ∀ i, Fin (smallC i) ↪ Fin (C i)),
        letI : ∀ i, Fact (0 < smallC i) := fun i ↦ ⟨hsmall i⟩
        (∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv smallC i
          (S ∘ selectorProductCoordinateInclusion smallC C e) x) = 1) ∧
        (∀ x, Function.Injective (selectorOldSecondForm smallC
          (S ∘ selectorProductCoordinateInclusion smallC C e)
          (hS.comp (selectorProductCoordinateInclusion_contMDiff smallC C e)) x)) ∧
        (∀ x v, ε * ‖v‖ ≤ ‖selectorOldSecondForm smallC
          (S ∘ selectorProductCoordinateInclusion smallC C e)
          (hS.comp (selectorProductCoordinateInclusion_contMDiff smallC C e)) x v‖) ∧
        ∀ x, ε ≤ leastSingularNorm (LinearMap.toContinuousLinearMap (selectorOldSecondForm smallC
          (S ∘ selectorProductCoordinateInclusion smallC C e)
          (hS.comp (selectorProductCoordinateInclusion_contMDiff smallC C e)) x)) := by
  let : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have h := hC i; omega⟩
  have hcollar := exact_analytic_hopf_collar m hm (freeHopfOldDimensions C)
    (fun i ↦ hC i.castSucc)
  rw [free_symmetric_column_count] at hcollar
  change ∃ r0 : ℝ, 0 < r0 ∧
    ∃ G : ℝ × FreeHopfProduct (freeHopfOldDimensions C) →
      EuclideanSpace ℝ (Fin (symmetricTensorDimension m + m + 1)),
      AnalyticHopfCollarProperties (freeHopfOldDimensions C) r0 G at hcollar
  obtain ⟨r0, hr0, G, hG⟩ := hcollar
  obtain ⟨S, hS, hGram, hinj, ε, hε, hbound⟩ :=
    whole_product_selector_from_actual_collar m hm C hC r0 hr0 G hG
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (SymmetricSquare (EuclideanSpace ℝ (Fin m))) :=
    symmetric_square_nontrivial
  refine ⟨S, hS, ε, hε, hGram, hinj, hbound, ?_, ?_⟩
  · intro x
    exact ((least_singular_norm_bound
      (selectorOldSecondForm C S hS x).toContinuousLinearMap).2.2 ε).mpr (hbound x)
  · intro smallC hsmall e
    let : ∀ i, Fact (0 < smallC i) := fun i ↦ ⟨hsmall i⟩
    have hrestriction :=
      selectorProductCoordinateInclusion_properties smallC C e S hS hGram hinj ε hbound
    refine ⟨selectorProductCoordinateInclusion_gram smallC C e S hGram,
      hrestriction.1, hrestriction.2, ?_⟩
    intro x
    exact ((least_singular_norm_bound (LinearMap.toContinuousLinearMap
      (selectorOldSecondForm smallC (S ∘ selectorProductCoordinateInclusion smallC C e)
        (hS.comp (selectorProductCoordinateInclusion_contMDiff smallC C e)) x))).2.2 ε).mpr
      (hrestriction.2 x)

end GlobalEmbedding.Paper
