import Probes.Round4UniformTemplateBlock
import Probes.ActualQuantitativeAdaptedRefinement

/-!
A uniform finite refinement for the numerical allowed class. The finite
dictionary, construction radius, total piece bound and all cutoff costs are
fixed before the actual map/tensor field. Every selected template is valid
on the whole source of each of its actual adapted charts. The cutoffs are
the existing translated-bump formula, with its genuine partition identity
and dimension-only local multiplicity, not an assumed partition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric Function
open scoped TensorProduct Topology ContDiff NNReal BigOperators
namespace GlobalEmbedding.Continuation
attribute [local instance] Classical.propDecidable
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance refinementRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance refinementSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance refinementTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance refinementTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

theorem round4_uniform_template_refinement_before_fields
    (hdim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (modelRadius rho : ℝ) (hrho : 0 < rho) (L : ℝ≥0)
    (hradius : rho ≤ round4UniformTemplateRadius D V hdim R mu c H hmu hc / ((L : ℝ)+1)) :
    let C := actualUniformPhaseTemplateProvider D V hdim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V hdim R mu c H hmu hc
    let factor := actualPhaseRefinementFactor eta C.covectorBound
    let r := rho/factor
    ∃ pieceBound : ℕ, ∀
      (f : X → (SymmetricSquare D →L[ℝ] V) × (D →L[ℝ] D →L[ℝ] ℝ))
      (O K : Set X) (center : X),
      IsOpen O → LipschitzOnWith L f O → K ⊆ closedBall center modelRadius →
      (∀ x ∈ K, ball x rho ⊆ O) →
      (∀ x ∈ K, f x ∈ actualAllowedPhaseTensorData D V R mu c H) →
      ∃ (s : Finset X) (pick : s → C.indices)
        (charts : ∀ x : s, ∀ a, Round4UniformTemplateChart hdim R mu c H hmu hc
          f O x.val rho (pick x) a) (W : Set X),
        s.card ≤ pieceBound ∧ (↑s : Set X) ⊆ K ∧
        (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) ∧
        (∀ x ∈ K, ∃ z ∈ s, dist x z ≤ r) ∧ IsOpen W ∧ K ⊆ W ∧
        (∀ x ∈ W, ∑ z ∈ s, actualRefinementCutoff X s r z x = 1) ∧
        (∀ (z : s) a,
          tsupport (actualRefinementCutoff X s r z.val) ⊆ (charts z a).chart.source) ∧
        (∀ z : s, ContDiff ℝ ∞ (actualRefinementCutoff X s r z.val) ∧
          ∀ x, 0 ≤ actualRefinementCutoff X s r z.val x ∧
            actualRefinementCutoff X s r z.val x ≤ 1) ∧
        (∀ x : X, (s.filter (fun z => x ∈ tsupport (actualRefinementCutoff X s r z))).card ≤
          5^Module.finrank ℝ X) ∧
        (∀ (j : ℕ) (weight : ℝ), 0 ≤ weight → weight ≤ rho → ∀ (z : s) (x : X),
          weight^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r z.val) x‖ ≤
            factor^j * actualRefinementCutoffJetCost X j) := by
  classical
  intro C eta factor r
  have heta : 0 < eta := (round4UniformTemplateCovectorLower_spec D V hdim R mu c H hmu hc).1
  have hfactor : 0 < factor := actualPhaseRefinementFactor_pos heta C.covectorBound_pos.le
  have hr : 0 < r := div_pos hrho hfactor
  obtain ⟨pieceBound, hCountBound⟩ := actual_exists_uniform_total_refinement_bound X modelRadius r hr
  refine ⟨pieceBound, ?_⟩
  intro f O K center hO hf hKball hbuffer hallowed
  have hK : TotallyBounded K := (isCompact_closedBall center modelRadius).totallyBounded.subset hKball
  obtain ⟨s, hsK, hsep, hcover, hcount⟩ := actual_exists_finite_bounded_refinement K hK r hr
  have hchoice (z : s) : ∃ i : C.indices, ∀ a,
      Nonempty (Round4UniformTemplateChart hdim R mu c H hmu hc f O z.val rho i a) := by
    apply round4_uniform_template_block hdim R mu c H hmu hc f O L hf z.val
      (hbuffer z.val (hsK z.property) (mem_ball_self hrho))
      (hallowed z.val (hsK z.property)) rho hrho (hbuffer z.val (hsK z.property)) hradius
  choose pick hpick using hchoice
  let charts := fun (z : s) a => Classical.choice (hpick z a)
  let W : Set X := {x | 1/2 < actualRefinementRawSum X s r x}
  have hW : IsOpen W := isOpen_lt continuous_const (actualRefinementRawSum_contDiff X s r).continuous
  have hKW : K ⊆ W := by
    intro x hx
    have hh := actualRefinementRawSum_lower_on_cover X s r hr K hcover x hx
    change 1/2 < actualRefinementRawSum X s r x
    linarith
  refine ⟨s, pick, charts, W,
    hCountBound s center (fun z hz => hKball (hsK hz)) hsep, hsK, hsep, hcover, hW, hKW, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [actualRefinementCutoff_sum]
    exact actualRefinementReciprocal_exact _ (le_of_lt hx)
  · intro z a
    apply (actualRefinementCutoff_tsupport X s r hr z.val).trans
    apply (closedBall_subset_ball (by linarith : 2*r < 4*r)).trans
    have hrad : 4*r = actualEuclideanPhaseRadius eta C.covectorBound rho :=
      actualPhaseRefinementFactor_radius eta C.covectorBound rho
    rw [hrad]
    exact (charts z a).inner
  · intro z
    exact ⟨actualRefinementCutoff_contDiff X s r z.val, fun x =>
      ⟨actualRefinementCutoff_nonneg X s r z.val x,
        actualRefinementCutoff_le_one X s r z.val z.property x⟩⟩
  · intro x
    apply (Finset.card_le_card ?_).trans (hcount x)
    intro z hz
    obtain ⟨hzin, hx⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hzin, ?_⟩
    have hh := actualRefinementCutoff_tsupport X s r hr z hx
    simpa only [mem_closedBall, dist_comm] using hh
  · intro j weight hweight hwrho z x
    have hb := actualRefinementCutoff_weighted_jet X s r hr hsep z.val x j
    have he : rho = factor*r := by
      dsimp only [r]
      field_simp
    calc
      _ ≤ rho^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r z.val) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hweight hwrho j) (norm_nonneg _)
      _ = factor^j*(r^j*‖iteratedFDeriv ℝ j (actualRefinementCutoff X s r z.val) x‖) := by
        conv_lhs => arg 1; rw [he, mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (pow_nonneg hfactor.le j)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_uniform_template_refinement_before_fields
