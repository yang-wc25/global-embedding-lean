import Probes.Round4UniformTemplateRefinement
import Probes.Round4RefinementSquareCutoffs
import Probes.Round4SupportedTemplateAmplitudes

/-!
An actual finite positive tensor decomposition from the numerical allowed
class, with one fixed construction radius. The same separated centers and
actual phase charts now carry globally smooth square cutoffs and globally
smooth supported square-root amplitudes. Their squared rank-one sum equals
the original tensor exactly on a genuine neighborhood of the covered set.
Every derivative constant for the cutoffs and the total/local piece counts
is fixed before the actual field and has no atlas-count input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric Function
open scoped TensorProduct Topology ContDiff NNReal BigOperators
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance squareFamilyRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance squareFamilySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) := Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance squareFamilyTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance squareFamilyTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

theorem round4_uniform_template_square_family_before_fields
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (modelRadius rho : ℝ) (hrho : 0 < rho) (L : ℝ≥0)
    (hradius : rho ≤ round4UniformTemplateRadius D V hdim R mu c H hmu hc / ((L : ℝ)+1)) :
    let C := actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc
    let factor := actualPhaseRefinementFactor eta C.covectorBound
    let r := rho/factor
    let hr : 0 < r := div_pos hrho
      (actualPhaseRefinementFactor_pos
        (round4UniformTemplateCovectorLower_spec D V hdim R mu c H hmu hc).1 C.covectorBound_pos.le)
    ∃ pieceBound : ℕ, ∀
      (f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
      (O K : Set X) (center : X),
      IsOpen O → LipschitzOnWith L f O →
      ContDiffOn ℝ ∞ (fun x => (f x).2) O →
      (∀ x ∈ O, ∀ v w, (f x).2 v w = (f x).2 w v) →
      K ⊆ closedBall center modelRadius →
      (∀ x ∈ K, ball x rho ⊆ O) →
      (∀ x ∈ K, f x ∈ actualAllowedPhaseTensorData D V R mu c H) →
      ∃ (s : Finset X) (pick : s → C.indices)
        (charts : ∀ x : s, ∀ a, Round4UniformTemplateChart hdim R mu c H hmu hc
          f O x.val rho (pick x) a) (W : Set X),
        let chi := round4RefinementSquareCutoff X s r
        let amplitude := fun (z : s) a => round4TemplateSupportedScalar
          (C.template (pick z)) (chi z) (fun x => (f x).2) a
        s.card ≤ pieceBound ∧ (↑s : Set X) ⊆ K ∧ IsOpen W ∧ K ⊆ W ∧
        (∀ x ∈ W, ∑ z : s, chi z x ^ 2 = 1) ∧
        (∀ z : s, ContDiff ℝ ∞ (chi z)) ∧
        (∀ x : X, (activeCutoffIndices chi x).card ≤ 5^Module.finrank ℝ X) ∧
        (∀ (z : s) (j : ℕ) (x : X), ‖iteratedFDeriv ℝ j (chi z) x‖ ≤
          round4RefinementSquareProfile X r hr j) ∧
        (∀ (z : s) a, ContDiff ℝ ∞ (amplitude z a) ∧
          tsupport (amplitude z a) ⊆ (charts z a).chart.source) ∧
        (∀ x ∈ W, (∑ z : s, continuousRankOneReconstruct (C.template (pick z)).covectors
          (fun a => amplitude z a x ^ 2)) = (f x).2) := by
  classical
  intro C eta factor r hr
  obtain ⟨pieceBound, hRefine⟩ := round4_uniform_template_refinement_before_fields
    (Ep := Ep) hdim R mu c H hmu hc modelRadius rho hrho L hradius
  refine ⟨pieceBound, ?_⟩
  intro f O K center hO hf hg hsymm hKball hbuffer hallowed
  obtain ⟨s, pick, charts, W0, hcard, hsK, hsep, hcover, hW0, hKW0,
    hpart0, hsup0, hsm0, hcount0, hcut0⟩ := hRefine f O K center hO hf hKball hbuffer hallowed
  have hsquare := round4_refinement_square_cutoffs X s r hr hsep
  obtain ⟨W, hW, hKW, hpart⟩ := round4_refinement_square_partition_near X s r hr K hcover
  let chi := round4RefinementSquareCutoff X s r
  have hsupport (z : s) (a : EdgePair (Module.finrank ℝ D + 1)) :
      tsupport (chi z) ⊆ (charts z a).chart.source := by
    apply (hsquare.2.1 z).trans
    apply (closedBall_subset_ball (by linarith : 2*r < 4*r)).trans
    have hrad : 4*r = actualEuclideanPhaseRadius eta C.covectorBound rho :=
      actualPhaseRefinementFactor_radius eta C.covectorBound rho
    rw [hrad]
    exact (charts z a).inner
  refine ⟨s, pick, charts, W, hcard, hsK, hW, hKW, hpart, hsquare.1,
    hsquare.2.2.1, hsquare.2.2.2, ?_, ?_⟩
  · intro z a
    have h := round4_template_supported_scalar_smooth (C.template (pick z)) (chi z)
      (fun x => (f x).2) O hO (hsquare.1 z) hg
      ((hsupport z a).trans (charts z a).source_domain)
      (fun x hx => (charts z a).tensor_domain x (hsupport z a hx)) a
    exact ⟨h.1, h.2.trans (hsupport z a)⟩
  · intro x hx
    let a0 : EdgePair (Module.finrank ℝ D + 1) :=
      ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; omega⟩
    apply round4_template_square_family_reconstruct (fun z => C.template (pick z)) chi
      (fun x => (f x).2) x (hpart x hx)
    · intro z hz
      exact (charts z a0).tensor_domain x (hsupport z a0 hz)
    · intro z hz
      exact hsymm x ((charts z a0).source_domain (hsupport z a0 hz))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_uniform_template_square_family_before_fields
