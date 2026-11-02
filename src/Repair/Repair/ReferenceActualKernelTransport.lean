import Repair.ReferenceKernelTransport
import Repair.ReferenceRehostedChart
import Probes.ActualSecondaryInverseTensor
import Probes.Round4ActualTemplateField

/-!
# Numerical primary kernel reserves in every actual observing host

The inverse coordinate map, its spatial differential equivalence, the
normal-Hessian tensor identity, and the literal weighted phase differential
are all produced from the original two charts.  The final bound consumes
only the owner's actual template membership and the original inverse
transition bound; no reserve on the observing kernel is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance actualReferenceKernelRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance actualReferenceKernelSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

section Lift
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem repair_reference_hessian_lift_transport
    (B : E →L[ℝ] E →L[ℝ] V) (A : E →L[ℝ] E) :
    actualHessianLift (B.bilinearComp A A) =
      (actualHessianLift B).comp (symmetricSquareMapL A) := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w =>
      change symmetrizedHessianJet (B.bilinearComp A A) (symmetricSquareProduct E v w) =
        symmetrizedHessianJet B (symmetricSquareMapL A (symmetricSquareProduct E v w))
      rw [symmetricSquareMapL_product,symmetrizedHessianJet_product,symmetrizedHessianJet_product]
      rfl
    | add a b ha hb =>
      change actualHessianLift (B.bilinearComp A A) (symmetricSquareQuotient E (a+b)) =
        ((actualHessianLift B).comp (symmetricSquareMapL A)) (symmetricSquareQuotient E (a+b))
      simp only [map_add]
      exact congrArg₂ (·+·) ha hb
end Lift

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem repair_reference_actual_phase_operator_transport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (he0 : ∀ p, e0 p ∈ IsManifold.maximalAtlas I ∞ M)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hPhi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hMap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hCoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (z : X) (hz : z ∈ U) :
    round4ActualPhaseOperatorInChart F e1 z =
      (round4ActualPhaseOperatorInChart F e0 (actualSourceChartTransition e0 e1 z)).comp
        (symmetricSquareMapL (actualJointSpatialJacobian (actualSourceChartTransition e0 e1) z)) := by
  unfold round4ActualPhaseOperatorInChart
  rw [actual_normal_hessian_true_chart_transition F hF e0 e1 he0 U W hU hW
    hJoint hPhi hMap hCoord z hz,repair_reference_hessian_lift_transport]

theorem repair_reference_transition_spatial_equiv
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (z : X) (hz : z ∈ (repairReferenceHostTransition observer owner).source) :
    ∃ A : D ≃L[ℝ] D,
      A.toContinuousLinearMap = actualJointSpatialJacobian (repairReferenceHostTransition observer owner) z ∧
      A.symm.toContinuousLinearMap =
        fderiv ℝ (observer ∘ owner.symm) (owner (observer.symm z.2)) := by
  let b := repairReferenceHostTransition (Ep := Ep) observer owner
  have ht := repair_reference_host_transition_smooth (Ep := Ep) observer owner hObserver hOwner
  let J := actualJointSpatialJacobian b z
  let S := actualJointSpatialJacobian b.symm (b z)
  have hSJ : S.comp J = ContinuousLinearMap.id ℝ D :=
    actual_joint_spatial_jacobian_inverse b ht.1 ht.2 (fun _ _ => rfl) z hz
  have hJS : J.comp S = ContinuousLinearMap.id ℝ D := by
    have h := actual_joint_spatial_jacobian_inverse b.symm ht.2 ht.1 (fun _ _ => rfl)
      (b z) (b.map_source hz)
    simpa only [OpenPartialHomeomorph.symm_symm,b.left_inv hz,J,S] using h
  let A := ContinuousLinearEquiv.equivOfInverse J S
    (fun v => congrArg (fun L : D →L[ℝ] D => L v) hSJ)
    (fun v => congrArg (fun L : D →L[ℝ] D => L v) hJS)
  exact ⟨A,rfl,rfl⟩

theorem repair_reference_actual_weighted_phase_differential
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (xi : D →L[ℝ] ℝ) (weight : ℝ)
    (z : X) (hz : z ∈ (repairReferenceHostTransition observer owner).source) :
    fderiv ℝ (fun x : D => weight*xi (owner (observer.symm x))) z.2 =
      weight • xi.comp (actualJointSpatialJacobian (repairReferenceHostTransition observer owner) z) := by
  let b := repairReferenceHostTransition (Ep := Ep) observer owner
  let t : D → D := owner ∘ observer.symm
  have ht : DifferentiableAt ℝ t z.2 := by
    have h := ((repair_reference_host_transition_smooth (Ep := Ep) observer owner hObserver hOwner).1.snd
      |>.contDiffAt (b.open_source.mem_nhds hz)).comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
    exact h.differentiableAt (by simp)
  have hscale : fderiv ℝ (weight • (xi ∘ t)) z.2 = weight • fderiv ℝ (xi ∘ t) z.2 :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := xi ∘ t) weight) z.2
  change fderiv ℝ (weight • (xi ∘ t)) z.2 = _
  rw [hscale,fderiv_comp z.2 xi.differentiableAt ht,ContinuousLinearMap.fderiv]
  rfl

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

/-- The exact original observing-host kernel bound, produced from one
actual owner template and the original backward transition bound. -/
theorem repair_reference_actual_primary_kernel_reserve
    (C : UniformActualGoodDictionaryCover K) (T : ℝ) (hT : 0 < T)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (W : Set X) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (owner.symm z.2)) W)
    (z : X) (hz : z ∈ (repairReferenceHostTransition observer owner).source)
    (hzw : repairReferenceHostTransition observer owner z ∈ W)
    (hInverse : ‖fderiv ℝ (observer ∘ owner.symm) (owner (observer.symm z.2))‖ ≤ T)
    (i : C.indices) (a : EdgePair (Module.finrank ℝ D+1))
    (hTemplate : round4ActualPhaseOperatorInChart F (fun _ => owner)
      (repairReferenceHostTransition observer owner z) ∈ (C.template i).operatorDomain)
    (weight : ℝ) (hWeight : weight ≠ 0) :
    ∀ v, (C.restrictionReserve/T^2)*‖v‖ ≤
      ‖covectorRestriction (round4ActualPhaseOperatorInChart F (fun _ => observer) z)
        (fderiv ℝ (fun x : D => weight*((C.template i).covectors a) (owner (observer.symm x))) z.2) v‖ := by
  let b := repairReferenceHostTransition (Ep := Ep) observer owner
  let U := b.source ∩ b ⁻¹' W
  have hU : IsOpen U := b.isOpen_inter_preimage hW
  have ht := repair_reference_host_transition_smooth (Ep := Ep) observer owner hObserver hOwner
  obtain ⟨A,hA,hAi⟩ := repair_reference_transition_spatial_equiv observer owner hObserver hOwner z hz
  have hOperator := repair_reference_actual_phase_operator_transport F hF
    (fun _ => owner) (fun _ => observer) (fun _ => hOwner) U W hU hW hJoint
    (ht.1.mono inter_subset_left) (fun _ hy => hy.2) (fun _ hy => hy.1.2) z ⟨hz,hzw⟩
  have hPhase := repair_reference_actual_weighted_phase_differential observer owner hObserver hOwner
    ((C.template i).covectors a) weight z hz
  have hLower := repair_reference_weighted_template_kernel_transport C i a
    (round4ActualPhaseOperatorInChart F (fun _ => owner) (b z)) hTemplate A T hT
    (by rwa [hAi]) weight hWeight
  have hJ : actualJointSpatialJacobian (actualSourceChartTransition
      (fun _ => owner) (fun _ => observer)) z = A.toContinuousLinearMap := hA.symm
  rw [hOperator,hPhase,hJ,← hA]
  exact hLower

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_actual_phase_operator_transport
#print axioms GlobalEmbedding.Continuation.repair_reference_transition_spatial_equiv
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_primary_kernel_reserve
