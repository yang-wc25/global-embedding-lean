import Smoothing.Round4OriginalPairLowClassAssembly

/-!
# Numerical data fixed before every actual reference field and atlas

Only the original low map/tensor budgets, allowed ellipticity and phase
margin, dimensions, model radius and buffer enter.  The same existing
Round4 formulas determine the template cover, normal and refinement radii,
cutoff profile and per-host piece count.  No host count or actual map is
stored in this numerical datum.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
open scoped TensorProduct ContDiff Topology NNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance factoryBudgetRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance factoryBudgetSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

structure RepairReferenceFactoryBudget (m d N : ℕ) where
  mapC3 : ℝ
  tensorC1 : ℝ
  phaseMargin : ℝ
  tensorLower : ℝ
  firstLower : ℝ
  modelRadius : ℝ
  buffer : ℝ
  mapC3_nonneg : 0 ≤ mapC3
  tensorC1_nonneg : 0 ≤ tensorC1
  phaseMargin_pos : 0 < phaseMargin
  tensorLower_pos : 0 < tensorLower
  firstLower_pos : 0 < firstLower
  buffer_pos : 0 < buffer
  templateDim : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1)))
  ambientDim : (m+1)*(m+2)/2 < N

namespace RepairReferenceFactoryBudget
variable {m d N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
private local instance factoryBudgetFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance factoryBudgetFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance factoryBudgetHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance factoryBudgetHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance factoryBudgetTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance factoryBudgetTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

def nativeMap3 (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  actualOriginalMapJetCost (m+1) d N 1*b.mapC3
theorem nativeMap3_nonneg (b : RepairReferenceFactoryBudget m d N) : 0 ≤ b.nativeMap3 :=
  mul_nonneg (actualOriginalMapJetCost_nonneg (m+1) d N 1) b.mapC3_nonneg
def nativeTensor1 (b : RepairReferenceFactoryBudget m d N) : ℝ≥0 :=
  ⟨round4OriginalTensorJetCost (m+1) d 1*b.tensorC1,
    mul_nonneg (round4OriginalTensorJetCost_nonneg (m+1) d 1) b.tensorC1_nonneg⟩
def operatorBound (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  ‖actualHessianLift (E := D) (F := V)‖*b.nativeMap3
def lipschitz (b : RepairReferenceFactoryBudget m d N) : ℝ≥0 :=
  round4ActualTemplateFieldLipschitz m N b.firstLower b.nativeMap3 b.nativeMap3
    b.firstLower_pos b.nativeMap3_nonneg b.nativeMap3_nonneg b.nativeTensor1
def cover (b : RepairReferenceFactoryBudget m d N) :=
  actualUniformPhaseTemplateProvider D V b.templateDim b.operatorBound b.phaseMargin b.tensorLower
    b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos
def covectorLower (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  round4UniformTemplateCovectorLower D V b.templateDim b.operatorBound b.phaseMargin b.tensorLower
    b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos
def forward (b : RepairReferenceFactoryBudget m d N) : ℝ := 2*(1+2*b.cover.covectorBound)
def inverse (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  2*actualPhaseInverseConstant b.covectorLower (2*b.cover.covectorBound)
def normalRadius (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  round4NativeNormalRadius m N b.firstLower b.forward b.inverse b.cover.restrictionReserve b.nativeMap3
def firstReserve (b : RepairReferenceFactoryBudget m d N) : ℝ := b.firstLower/b.forward^2
def transverseReserve (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  (b.cover.restrictionReserve/(b.forward^2*actualIncrementSortedSymmetricConstant m))^2
def radius (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  round4UniformNormalRefinementRadius (N := N) b.templateDim b.operatorBound b.phaseMargin b.tensorLower
    b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos b.buffer b.firstLower b.nativeMap3 b.lipschitz
def cutoffRadius (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  b.radius/actualPhaseRefinementFactor b.covectorLower b.cover.covectorBound
def pieceBound (b : RepairReferenceFactoryBudget m d N) : ℕ :=
  round4UniformNormalPieceBound (N := N) Ep b.templateDim b.operatorBound b.phaseMargin b.tensorLower
    b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos b.modelRadius b.buffer b.firstLower b.nativeMap3
    b.nativeTensor1 b.buffer_pos b.firstLower_pos b.nativeMap3_nonneg
def cutoffProfile (b : RepairReferenceFactoryBudget m d N) : ℕ → ℝ :=
  round4UniformNormalCutoffProfile (N := N) Ep b.templateDim b.operatorBound b.phaseMargin b.tensorLower
    b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos b.buffer b.firstLower b.nativeMap3
    b.nativeTensor1 b.buffer_pos b.firstLower_pos b.nativeMap3_nonneg

theorem radius_pos (b : RepairReferenceFactoryBudget m d N) : 0 < b.radius :=
  (round4UniformNormalRefinementRadius_spec b.templateDim b.operatorBound b.phaseMargin b.tensorLower
    b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos b.buffer b.firstLower b.nativeMap3 b.lipschitz
    b.buffer_pos b.firstLower_pos b.nativeMap3_nonneg).1
theorem cutoffRadius_pos (b : RepairReferenceFactoryBudget m d N) : 0 < b.cutoffRadius :=
  div_pos b.radius_pos (actualPhaseRefinementFactor_pos
    (round4UniformTemplateCovectorLower_spec D V b.templateDim b.operatorBound b.phaseMargin b.tensorLower
      b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos).1 b.cover.covectorBound_pos.le)

end RepairReferenceFactoryBudget
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.RepairReferenceFactoryBudget.radius_pos
#print axioms GlobalEmbedding.Continuation.RepairReferenceFactoryBudget.cutoffRadius_pos
