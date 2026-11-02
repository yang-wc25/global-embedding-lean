import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates

/-!
# A uniform phase-template provider from the original bounded data class

The compact set is now constructed from numerical upper, ellipticity and
best-phase lower bounds. It is chosen before the actual map, tensor, atlas,
scales and observation order. Every selected covector has its own actual
kernel reserve; no best-phase bound is assigned to an arbitrary phase.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
open scoped TensorProduct Topology
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance providerRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance providerSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable (E V : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private local instance providerTensorNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private local instance providerTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def actualAllowedPhaseTensorData (R mu c H : ℝ) :
    Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ)) :=
  {B : SymmetricSquare E →L[ℝ] V | ‖B‖ ≤ R ∧ mu ≤ bestPhaseSupremum B} ×ˢ
    boundedPositiveTensorSet E c H

theorem actualAllowedPhaseTensorData_isCompact
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) :
    IsCompact (actualAllowedPhaseTensorData E V R mu c H) :=
  (bounded_phase_operator_set_compact hdim R mu).prod (boundedPositiveTensorSet_isCompact c H)

theorem actual_exists_uniform_phase_template_provider
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) :
    Nonempty (UniformActualGoodDictionaryCover (E := E) (F := V)
      (actualAllowedPhaseTensorData E V R mu c H)) := by
  apply compact_actual_good_dictionary_uniform_cover _
    (actualAllowedPhaseTensorData_isCompact E V hdim R mu c H)
  · intro z hz
    obtain ⟨xi,_,hgood⟩ := actual_good_covector_of_positive_bestPhaseSupremum hdim z.1
      (hmu.trans_le hz.1.2)
    exact ⟨xi,hgood⟩
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact boundedPositiveTensorSet_posDef hc hz.2

/-- One fixed provider for the entire numerical allowed class. -/
def actualUniformPhaseTemplateProvider
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c) :
    UniformActualGoodDictionaryCover (E := E) (F := V)
      (actualAllowedPhaseTensorData E V R mu c H) :=
  Classical.choice (actual_exists_uniform_phase_template_provider E V hdim R mu c H hmu hc)

/-- The SAME native second form and input tensor select a member of the
fixed provider. Positivity and the selected canonical kernel reserve are
outputs for every actual dictionary covector, including its true inverse. -/
theorem actual_uniform_provider_supplies_chosen_reserves
    (hdim : 2 ≤ Module.finrank ℝ E) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (B : SymmetricSquare E →L[ℝ] V) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ‖B‖ ≤ R) (hphase : mu ≤ bestPhaseSupremum B)
    (hsymm : ∀ v w, A v w = A w v) (hpos : ∀ v, c*‖v‖^2 ≤ A v v) (hA : ‖A‖ ≤ H) :
    let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
    ∃ i : C.indices,
      B ∈ (C.template i).operatorDomain ∧ A ∈ (C.template i).tensorDomain ∧
      ∀ a,
        LinearSecondFormGoodCovector B.toLinearMap ((C.template i).covectors a).toLinearMap ∧
        (∀ z, C.restrictionReserve*‖z‖ ≤ ‖covectorRestriction B ((C.template i).covectors a) z‖) ∧
        C.coefficientReserve ≤ (C.template i).coefficients A a ∧
        ∃ e : SymmetricSquare ((C.template i).covectors a).ker ≃L[ℝ]
            LinearMap.range (covectorRestriction B ((C.template i).covectors a)).toLinearMap,
          (∀ z, (e z).val = covectorRestriction B ((C.template i).covectors a) z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ C.restrictionReserve⁻¹ := by
  dsimp only
  let C := actualUniformPhaseTemplateProvider E V hdim R mu c H hmu hc
  have hmem : (B,A) ∈ actualAllowedPhaseTensorData E V R mu c H :=
    ⟨⟨hB,hphase⟩,hsymm,hpos,hA⟩
  obtain ⟨i,hiB,hiA⟩ := C.covers (B,A) hmem
  refine ⟨i,hiB,hiA,?_⟩
  intro a
  obtain ⟨hg,hb,e,he,heB⟩ := (C.template i).operator_control B hiB a
  refine ⟨hg,fun z => (mul_le_mul_of_nonneg_right (C.bounds i).1 (norm_nonneg z)).trans (hb z),
    (C.bounds i).2.1.trans ((C.template i).coefficient_control A hiA a),e,he,?_⟩
  exact heB.trans ((inv_le_inv₀ (C.template i).restrictionReserve_pos C.restrictionReserve_pos).2
    (C.bounds i).1)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_exists_uniform_phase_template_provider
#print axioms GlobalEmbedding.Continuation.actual_uniform_provider_supplies_chosen_reserves
