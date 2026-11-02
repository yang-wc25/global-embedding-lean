import Repair.IncrementGivenPhaseExtraction
import Probes.ActualIncrementOriginalPrimitiveBinding
import Probes.ActualIncrementOriginalCoreFields

/-!
# The actual general phase differential in original spatial coordinates

The original manifold covector is identified with the spatial components
of the full joint coordinate differential for an arbitrary original phase.
No linear-template or owner-phase assumption is introduced. This identity
retains the actual inverse-chart tangent vectors, so parameter derivatives
of the resulting spatial covector remain the original mixed derivatives.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.FaithfulIncrements

theorem original_model_source_single (n d : ℕ) (r : Fin n) :
    parameterTensorModelEquiv n d
      ((0 : EuclideanSpace ℝ (Fin d)),EuclideanSpace.single r 1) =
      Pi.single (Fin.castAdd d r) (1 : ℝ) := by
  apply (parameterTensorModelEquiv n d).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply,parameterTensorModelEquiv_symm_apply]
  ext s
  · simp only [incrementsOriginalParameterPoint,Pi.single_apply,Pi.zero_apply]
    split_ifs with h
    · have hh := congrArg Fin.val h
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
      omega
    · rfl
  · simp [incrementsOriginalSourcePoint,EuclideanSpace.single,Pi.single_apply]

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Y" => Fin (n+d) → ℝ
local notation "I" => 𝓘(ℝ,Es)

/-- General chain rule for the original phase and actual source basis. -/
theorem original_phase_spatial_coordinates
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (y : Y) (hy : y ∈ actualOriginalPrimaryCoordinateOpen Data nu i) :
    incrementsOriginalPhaseCovectorCoordinates Data nu i y =
      incrementGivenSpatialExtraction n d (fderiv ℝ (actualOriginalJointPhase Data nu i) y) := by
  let a := parameterTensorModelEquiv n d
  let z := a.symm y
  let p := (Data.parameterChart i.2).symm z.1
  let c := Data.atlas.chart i.1
  let f : M → ℝ := fun x => Data.phase nu (p,x)
  have hyPhase : y ∈ actualOriginalPhaseOpen Data nu i :=
    ⟨hy.1,hy.1.1,hy.2⟩
  have hJoint : DifferentiableAt ℝ (actualOriginalJointPhase Data nu i) y :=
    ((actualOriginalJointPhase_contDiffOn Data hd hs nu i).contDiffAt
      ((actualOriginalPhaseOpen_open Data hd nu i).mem_nhds hyPhase)).differentiableAt (by simp)
  have hActive : (p,c.symm z.2) ∈
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := ⟨hy.1.2,hy.2⟩
  have hf : MDifferentiableAt I 𝓘(ℝ,ℝ) f (c.symm z.2) :=
    actual_original_phase_mdifferentiableAt Data hd hs nu p (c.symm z.2) hActive
  have hc : MDifferentiableAt I I c.symm z.2 :=
    mdifferentiableAt_symm_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_of_le (by simp) (hd.atlas_smooth.chart_mem i.1)) hy.1.1.1
  have hChain := mfderiv_comp z.2 hf hc
  rw [mfderiv_eq_fderiv] at hChain
  have hScalar (v : Es) :
      fderiv ℝ (f ∘ c.symm) z.2 v =
        incrementsOriginalPhaseCovector Data nu p (c.symm z.2)
          (mfderiv I I c.symm z.2 ((tangentSpaceCastModel I z.2).symm v)) := by
    have hh := congrArg (fun L => tangentSpaceCastModel 𝓘(ℝ,ℝ) (f (c.symm z.2))
      (L ((tangentSpaceCastModel I z.2).symm v))) hChain
    exact hh
  let insert : Es → Ep × Es := fun x => (z.1,x)
  have hInsert : HasFDerivAt insert (ContinuousLinearMap.inr ℝ Ep Es) z.2 := by
    simpa [insert] using
      (ContinuousLinearMap.inr ℝ Ep Es).hasFDerivAt.const_add (z.1,0)
  have hModel : HasFDerivAt (a ∘ insert)
      (a.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Ep Es)) z.2 :=
    a.hasFDerivAt.comp z.2 hInsert
  have hValue : (a ∘ insert) z.2 = y := a.apply_symm_apply y
  have hCompose : HasFDerivAt ((actualOriginalJointPhase Data nu i) ∘ (a ∘ insert))
      ((fderiv ℝ (actualOriginalJointPhase Data nu i) y).comp
        (a.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Ep Es))) z.2 := by
    have hJoint' : HasFDerivAt (actualOriginalJointPhase Data nu i)
        (fderiv ℝ (actualOriginalJointPhase Data nu i) y) ((a ∘ insert) z.2) := by
      rw [hValue]
      exact hJoint.hasFDerivAt
    exact hJoint'.comp z.2 hModel
  have hFunction : ((actualOriginalJointPhase Data nu i) ∘ (a ∘ insert)) = f ∘ c.symm := by
    funext x
    change Data.phase nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i
      (parameterTensorModelEquiv n d (z.1,x))) = _
    rw [actual_original_jointPoint_native]
    rfl
  rw [hFunction] at hCompose
  ext r
  change incrementsOriginalPhaseCovector Data nu p (c.symm z.2)
    (mfderiv I I c.symm z.2
      ((tangentSpaceCastModel I z.2).symm (EuclideanSpace.single r 1))) =
    fderiv ℝ (actualOriginalJointPhase Data nu i) y (Pi.single (Fin.castAdd d r) 1)
  rw [← hScalar,hCompose.fderiv]
  change fderiv ℝ (actualOriginalJointPhase Data nu i) y
    (a (0,EuclideanSpace.single r 1)) = _
  rw [original_model_source_single]

end GlobalEmbedding.Continuation.FaithfulIncrements
#print axioms GlobalEmbedding.Continuation.FaithfulIncrements.original_phase_spatial_coordinates

