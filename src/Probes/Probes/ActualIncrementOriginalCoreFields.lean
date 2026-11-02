import Probes.ActualIncrementOriginalCorePrimitives

/-! The literal original cutoff and given normal, in the actual original
native chart, with all joint derivative bounds produced by the frozen Core.
No derivative budget for either output field is a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es

theorem actual_original_jointPoint_native
    (Data : IncrementsOriginalNativeData n d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X) :
    incrementsOriginalJointPoint Data.atlas Data.parameterChart i (parameterTensorModelEquiv n d z) =
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) := by
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) = z :=
    (parameterTensorModelEquiv n d).symm_apply_apply z
  have hp := congrArg Prod.fst hprod
  have hx := congrArg Prod.snd hprod
  dsimp only at hp hx
  simp only [incrementsOriginalJointPoint,hp,hx]

def actualOriginalCutoffJetCost (n d j : ℕ) : ℝ :=
  ‖(ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toContinuousLinearMap‖ *
    linearModelFactor (parameterTensorModelEquiv n d) j * coordinateDimensionFactor (n+d) j

def actualOriginalNormalJetCost (n d N j : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
    linearModelFactor (parameterTensorModelEquiv n d) j * coordinateDimensionFactor (n+d) j

theorem actualOriginalCutoffJetCost_nonneg (n d j : ℕ) : 0 ≤ actualOriginalCutoffJetCost n d j :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
    (coordinateDimensionFactor_nonneg _ _)

theorem actualOriginalNormalJetCost_nonneg (n d N j : ℕ) : 0 ≤ actualOriginalNormalJetCost n d N j :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
    (coordinateDimensionFactor_nonneg _ _)

theorem actual_original_core_cutoff_native_jets
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data) (nu : Fin Data.primaryCount)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    let f := fun z : X => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,
      (Data.atlas.chart i.1).symm z.2)
    ContDiffOn ℝ ∞ f (actualOriginalPrimaryNativeOpen Data nu i) ∧
      ∀ k ≤ j, ∀ z, parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation Data nu i →
        ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ actualOriginalCutoffJetCost n d j*budget := by
  let cy := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  have hf : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalScalarCoordinates Data (Data.cutoff nu) i)
      (actualOriginalPrimaryCoordinateOpen Data nu i) := by
    intro i
    exact actual_original_primary_field_coordinate_smooth Data hd nu (Data.cutoff nu)
      (hs.cutoff_joint nu) cy.symm.toContinuousLinearMap i
  have hh := actual_original_primary_core_field_jets Data hd nu cy
    (incrementsOriginalScalarCoordinates Data (Data.cutoff nu)) hf j ell hell
    (actual_original_core_cutoff_le Data nu j ell) hfinite budget hbudget i
  have he : cy ∘ incrementsOriginalScalarCoordinates Data (Data.cutoff nu) i ∘
      parameterTensorModelEquiv n d = fun z : X => Data.cutoff nu
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) := by
    funext z
    change Data.cutoff nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i
      (parameterTensorModelEquiv n d z)) = _
    rw [actual_original_jointPoint_native]
  rw [he] at hh
  exact hh

theorem actual_original_core_normal_native_jets
    (Data : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data) (nu : Fin Data.primaryCount)
    (j : ℕ) (ell : ℝ) (hell : 0 < ell)
    (hfinite : incrementsOriginalCoreInputProfile Data j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile Data j ell).toReal ≤ budget)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    let f := fun z : X => Data.freeNormal nu ((Data.parameterChart i.2).symm z.1,
      (Data.atlas.chart i.1).symm z.2)
    ContDiffOn ℝ ∞ f (actualOriginalPrimaryNativeOpen Data nu i) ∧
      ∀ k ≤ j, ∀ z, parameterTensorModelEquiv n d z ∈ incrementsOriginalPrimaryEvaluation Data nu i →
        ell^k*‖iteratedFDeriv ℝ k f z‖ ≤ actualOriginalNormalJetCost n d N j*budget := by
  let cy := (EuclideanSpace.equiv (Fin N) ℝ).symm
  have hf : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu) i)
      (actualOriginalPrimaryCoordinateOpen Data nu i) := by
    intro i
    exact actual_original_primary_field_coordinate_smooth Data hd nu (Data.freeNormal nu)
      (hs.normal_joint nu) cy.symm.toContinuousLinearMap i
  have hh := actual_original_primary_core_field_jets Data hd nu cy
    (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (Data.freeNormal nu)) hf j ell hell
    (actual_original_core_normal_le Data nu j ell) hfinite budget hbudget i
  have he : cy ∘ incrementsOriginalMapCoordinates Data.atlas Data.parameterChart
      (Data.freeNormal nu) i ∘ parameterTensorModelEquiv n d = fun z : X => Data.freeNormal nu
        ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) := by
    funext z
    simp only [Function.comp_apply,incrementsOriginalMapCoordinates,
      ContinuousLinearEquiv.symm_apply_apply,actual_original_jointPoint_native,cy]
  rw [he] at hh
  exact hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_core_cutoff_native_jets
#print axioms GlobalEmbedding.Continuation.actual_original_core_normal_native_jets
