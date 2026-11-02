import Smoothing.Round4NormalCutoffCarrier
import Probes.Round4UniformTemplateBlock
import Probes.ActualQuantitativeAdaptedRefinement

/-! One actual normal serves the ENTIRE support ball of the refinement
cutoff. The construction radius obeys a numerical cap chosen before the
fields. The same chart, slices, coordinate, and high-order normal estimates
are retained for later finite-family assembly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct NNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance templateNormalRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance templateNormalSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance templateNormalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance templateNormalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance templateNormalTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
/-- This radius is numerical and precedes every actual field, center, atlas,
refinement index, and derivative order. -/
def round4UniformNormalRefinementRadius
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (buffer c0 K : ℝ) (Lip : ℝ≥0) : ℝ :=
  let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
  let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
  let B := 2*(1+2*C.covectorBound)
  let I := 2*actualPhaseInverseConstant eta (2*C.covectorBound)
  min buffer (min (round4UniformTemplateRadius D V templateDim R mu c H hmu hc/((Lip : ℝ)+1))
    (actualPhaseRefinementFactor eta C.covectorBound *
      round4NativeNormalRadius m N c0 B I C.restrictionReserve K/(4*B)))

theorem round4UniformNormalRefinementRadius_spec
    (templateDim : 2 ≤ Module.finrank ℝ D) (R mu c H : ℝ) (hmu : 0 < mu) (hc : 0 < c)
    (buffer c0 K : ℝ) (Lip : ℝ≥0) (hbuffer : 0 < buffer) (hc0 : 0 < c0) (hK : 0 ≤ K) :
    let C := actualUniformPhaseTemplateProvider D V templateDim R mu c H hmu hc
    let eta := round4UniformTemplateCovectorLower D V templateDim R mu c H hmu hc
    let B := 2*(1+2*C.covectorBound)
    let I := 2*actualPhaseInverseConstant eta (2*C.covectorBound)
    let rho := round4UniformNormalRefinementRadius (N := N) templateDim R mu c H hmu hc buffer c0 K Lip
    0 < rho ∧ rho ≤ buffer ∧
      rho ≤ round4UniformTemplateRadius D V templateDim R mu c H hmu hc/((Lip : ℝ)+1) ∧
      rho ≤ actualPhaseRefinementFactor eta C.covectorBound *
        round4NativeNormalRadius m N c0 B I C.restrictionReserve K/(4*B) := by
  intro C eta B I rho
  have heta : 0 < eta := (round4UniformTemplateCovectorLower_spec D V templateDim R mu c H hmu hc).1
  have hB : 0 < B := by have := C.covectorBound_pos; dsimp [B]; positivity
  have hI : 0 ≤ I := by
    have hM : 0 ≤ 2*C.covectorBound := mul_nonneg (by norm_num) C.covectorBound_pos.le
    have h := actualPhaseInverseConstant_one_le heta hM
    dsimp [I]
    linarith
  have hN := round4NativeNormalRadius_pos m N hc0 hB hI C.restrictionReserve_pos hK
  have hfactor := actualPhaseRefinementFactor_pos heta C.covectorBound_pos.le
  have hRad := (round4UniformTemplateRadius_spec D V templateDim R mu c H hmu hc).1
  refine ⟨?_,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩
  exact lt_min hbuffer (lt_min (div_pos hRad (by positivity))
    (div_pos (mul_pos hfactor hN) (mul_pos (by norm_num) hB)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4UniformNormalRefinementRadius_spec
