import Initialization.Phase.SelectorCoframe
import GlobalEmbedding.Targets.WholeProductSelectors

/-!
# A fixed, actually constructed selector phase reference

This package is produced from the already accepted whole-product selector
theorem.  It records its same native map and actual true old second form, plus
the actual orbit Hessian bound proved by compactness in `SelectorJets`.
No source manifold, chart, frequency, desired map, geometry bound or desired
phase margin occurs among the constructor's inputs.  In particular the selector
and both constants can be fixed once the color count is fixed, before `K,T`.
-/

noncomputable section
open Manifold GlobalEmbedding.Paper
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance selectorReferenceRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance selectorReferenceSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- Actual fixed selector data. The construction below supplies every field;
this structure is never asserted to be part of the original final hypotheses. -/
structure SelectorPhaseReference {m : ℕ} (C : Fin (m + 1) → ℕ)
    [∀ i, Fact (0 < C i)] where
  selector : FreeHopfProduct C → EuclideanSpace ℝ (Fin (closedAmbientDimension (m + 1)))
  smooth : ContMDiff (freeHopfModel C)
    𝓘(ℝ, EuclideanSpace ℝ (Fin (closedAmbientDimension (m + 1)))) ∞ selector
  gram : ∀ z, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i selector z) = 1
  margin : ℝ
  margin_pos : 0 < margin
  lower : ∀ z u, margin * ‖u‖ ≤ ‖selectorOldSecondForm C selector smooth z u‖
  secondBound : ℝ
  secondBound_pos : 0 < secondBound
  second_norm : ∀ z, ‖selectorIdealSecondJet C selector z‖ ≤ secondBound

/-- All selector phase reference data are supplied internally by the exact
accepted selector and the actual compact-Hessian bound. -/
theorem exists_selectorPhaseReference (m : ℕ) (hm : 1 ≤ m)
    (C : Fin (m + 1) → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have h := hC i; omega⟩
    Nonempty (SelectorPhaseReference C) := by
  letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have h := hC i; omega⟩
  obtain ⟨S, hS, ε, hε, hGram, _hinj, hbound, _hleast, _hsmall⟩ :=
    whole_product_hopf_selector m hm C hC
  obtain ⟨B, hB, hnorm⟩ := selectorIdealSecondJet_uniform_bound C S hS
  exact ⟨{
    selector := S
    smooth := hS
    gram := hGram
    margin := ε
    margin_pos := hε
    lower := hbound
    secondBound := B
    secondBound_pos := hB
    second_norm := hnorm }⟩

/-- One fixed choice, made before any initialization frequency or source data. -/
def selectorPhaseReference (m : ℕ) (hm : 1 ≤ m)
    (C : Fin (m + 1) → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have h := hC i; omega⟩
    SelectorPhaseReference C :=
  Classical.choice (exists_selectorPhaseReference m hm C hC)

namespace SelectorPhaseReference

variable {m : ℕ} {C : Fin (m + 1) → ℕ} [∀ i, Fact (0 < C i)]

/-- The positive fraction retained by actual two-jet stability. Its arguments
are the fixed selector reference and the fixed inverse-coframe reserve only. -/
def retainedMargin (P : SelectorPhaseReference C) (L : ℝ) : ℝ :=
  P.margin / (2 * (1 + L ^ 2))

theorem retainedMargin_pos (P : SelectorPhaseReference C) (L : ℝ) :
    0 < P.retainedMargin L := by
  unfold retainedMargin
  exact div_pos P.margin_pos (by positivity)

end SelectorPhaseReference

end GlobalEmbedding.Initialization
