import Probes.ActualUniformPhaseTemplateProvider
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
A numerical Lebesgue radius for the actual uniform good-dictionary provider.
The provider and this radius are selected from the original bounded operator /
positive tensor class, before any map, atlas, chart count, scale or jet order.
A first derivative bound then supplies a single frozen actual dictionary on
an entire source neighborhood, with the provider's genuine kernel and
coefficient reserves. No reserve for a preselected arbitrary phase is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric
open scoped TensorProduct Topology NNReal
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance radiusRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance radiusSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable (E V : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private local instance radiusTensorNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  inferInstance
private local instance radiusTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  inferInstance

theorem round4_exists_uniform_template_radius
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) :
    let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
    ∃ eps > 0, ∀ z ∈ actualAllowedPhaseTensorData E V R mu c H,
      ∃ i : C.indices,
        ball z eps ⊆ (C.template i).operatorDomain ×ˢ (C.template i).tensorDomain := by
  dsimp only
  let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
  let domains := fun i : C.indices =>
    (C.template i).operatorDomain ×ˢ (C.template i).tensorDomain
  apply lebesgue_number_lemma_of_metric
    (actualAllowedPhaseTensorData_isCompact E V hdim R mu c H)
    (c := domains)
  · intro i
    exact (C.template i).isOpen_operatorDomain.prod (C.template i).isOpen_tensorDomain
  · intro z hz
    obtain ⟨i, hi⟩ := C.covers z hz
    exact mem_iUnion.mpr ⟨i, hi⟩

def round4UniformTemplateRadius
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) : ℝ :=
  Classical.choose (round4_exists_uniform_template_radius E V hdim R mu c H hmu hc)

theorem round4UniformTemplateRadius_spec
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) :
    let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
    let eps := round4UniformTemplateRadius E V hdim R mu c H hmu hc
    0 < eps ∧ ∀ z ∈ actualAllowedPhaseTensorData E V R mu c H,
      ∃ i : C.indices,
        ball z eps ⊆ (C.template i).operatorDomain ×ˢ (C.template i).tensorDomain :=
  Classical.choose_spec (round4_exists_uniform_template_radius E V hdim R mu c H hmu hc)

/-- The local radius depends on a first derivative/Lipschitz bound and the
numerical allowed class. The chosen index works for the entire neighborhood. -/
theorem round4_uniform_template_on_lipschitz_neighborhood
    {X : Type*} [PseudoMetricSpace X]
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (f : X → (SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))
    (U : Set X) (L : ℝ≥0) (hf : LipschitzOnWith L f U)
    (x : X) (hx : x ∈ U) (hfx : f x ∈ actualAllowedPhaseTensorData E V R mu c H) :
    let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
    let rho := round4UniformTemplateRadius E V hdim R mu c H hmu hc / ((L : ℝ) + 1)
    0 < rho ∧ ∃ i : C.indices, ∀ y ∈ U ∩ ball x rho,
      (f y).1 ∈ (C.template i).operatorDomain ∧
      (f y).2 ∈ (C.template i).tensorDomain := by
  dsimp only
  have hspec := round4UniformTemplateRadius_spec E V hdim R mu c H hmu hc
  have hL : 0 < (L : ℝ) + 1 := by positivity
  refine ⟨div_pos hspec.1 hL, ?_⟩
  obtain ⟨i, hi⟩ := hspec.2 (f x) hfx
  refine ⟨i, fun y hy => hi ?_⟩
  apply mem_ball.mpr
  have hmul := (lt_div_iff₀ hL).mp (mem_ball.mp hy.2)
  calc
    dist (f y) (f x) ≤ (L : ℝ) * dist y x := hf.dist_le_mul y hy.1 x hx
    _ ≤ ((L : ℝ) + 1) * dist y x :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg
    _ < round4UniformTemplateRadius E V hdim R mu c H hmu hc := by
      simpa only [mul_comm] using hmul

/-- A native first derivative bound is enough. All output reserves concern
the actual field on the whole source ball and the same frozen dictionary. -/
theorem round4_uniform_template_from_first_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (f : X → (SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))
    (U : Set X) (hU : Convex ℝ U) (L : ℝ≥0)
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hDf : ∀ x ∈ U, ‖fderiv ℝ f x‖₊ ≤ L)
    (x : X) (hx : x ∈ U) (hfx : f x ∈ actualAllowedPhaseTensorData E V R mu c H) :
    let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
    let rho := round4UniformTemplateRadius E V hdim R mu c H hmu hc / ((L : ℝ) + 1)
    0 < rho ∧ ∃ i : C.indices, ∀ y ∈ U ∩ ball x rho,
      (f y).1 ∈ (C.template i).operatorDomain ∧
      (f y).2 ∈ (C.template i).tensorDomain ∧
      ∀ a,
        LinearSecondFormGoodCovector (f y).1.toLinearMap ((C.template i).covectors a).toLinearMap ∧
        (∀ z, C.restrictionReserve * ‖z‖ ≤
          ‖covectorRestriction (f y).1 ((C.template i).covectors a) z‖) ∧
        C.coefficientReserve ≤ (C.template i).coefficients (f y).2 a ∧
        (∀ eta : E →L[ℝ] ℝ, ‖eta - (C.template i).covectors a‖ < C.covectorRadius →
          LinearSecondFormGoodCovector (f y).1.toLinearMap eta.toLinearMap) ∧
        ∃ e : SymmetricSquare ((C.template i).covectors a).ker ≃L[ℝ]
            LinearMap.range (covectorRestriction (f y).1 ((C.template i).covectors a)).toLinearMap,
          (∀ z, (e z).val = covectorRestriction (f y).1 ((C.template i).covectors a) z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ C.restrictionReserve⁻¹ := by
  let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
  obtain ⟨hrho, i, hi⟩ := round4_uniform_template_on_lipschitz_neighborhood E V
    hdim R mu c H hmu hc f U L
    (Convex.lipschitzOnWith_of_nnnorm_fderiv_le hf hDf hU) x hx hfx
  refine ⟨hrho, i, ?_⟩
  intro y hy
  obtain ⟨hyB, hyA⟩ := hi y hy
  refine ⟨hyB, hyA, ?_⟩
  intro a
  obtain ⟨hg, hb, e, he, heB⟩ := (C.template i).operator_control (f y).1 hyB a
  refine ⟨hg,
    fun z => (mul_le_mul_of_nonneg_right (C.bounds i).1 (norm_nonneg z)).trans (hb z),
    (C.bounds i).2.1.trans ((C.template i).coefficient_control (f y).2 hyA a),
    ?_, e, he, ?_⟩
  · intro eta heta
    exact (C.template i).covector_ball_control (f y).1 hyB a eta
      (heta.trans_le (C.bounds i).2.2.1)
  · exact heB.trans
      ((inv_le_inv₀ (C.template i).restrictionReserve_pos C.restrictionReserve_pos).2
        (C.bounds i).1)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_exists_uniform_template_radius
#print axioms GlobalEmbedding.Continuation.round4_uniform_template_from_first_derivative
