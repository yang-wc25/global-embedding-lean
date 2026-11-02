import Repair.IncrementSignedNoncritical
import Repair.ReferenceActualKernelTransport

/-!
# Dominant signed reserves in every actual observing host

The actual phase differential and original normal-Hessian operator are
transported through the same genuine chart transition. The common signed
kernel margin loses the square of the original inverse-transition bound;
the noncritical covector norm loses one such factor. No adapted output
geometry or already transported lower bound is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance signedTransportRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance signedTransportSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

section Norm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem increment_covector_transition_norm_lower
    (A : E ≃L[ℝ] E) (xi : E →L[ℝ] ℝ) (mu T : ℝ) (hT : 0 < T)
    (hInverse : ‖A.symm.toContinuousLinearMap‖ ≤ T) (hLower : mu ≤ ‖xi‖) :
    mu/T ≤ ‖xi.comp A.toContinuousLinearMap‖ := by
  have he : xi = (xi.comp A.toContinuousLinearMap).comp A.symm.toContinuousLinearMap := by
    ext x
    exact (congrArg xi (A.apply_symm_apply x)).symm
  have hUpper : ‖xi‖ ≤ ‖xi.comp A.toContinuousLinearMap‖*T := by
    calc
      ‖xi‖ = ‖(xi.comp A.toContinuousLinearMap).comp A.symm.toContinuousLinearMap‖ := congrArg norm he
      _ ≤ ‖xi.comp A.toContinuousLinearMap‖*‖A.symm.toContinuousLinearMap‖ :=
        (xi.comp A.toContinuousLinearMap).opNorm_comp_le _
      _ ≤ _ := mul_le_mul_of_nonneg_left hInverse (norm_nonneg _)
  exact (div_le_iff₀ hT).mpr (hLower.trans hUpper)
end Norm

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem increment_actual_phase_covector_transport
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (psi : Ep × M → ℝ) (z : X)
    (hz : z ∈ (repairReferenceHostTransition observer owner).source)
    (hPhase : DifferentiableAt ℝ (fun x : D => psi (z.1,owner.symm x)) (owner (observer.symm z.2))) :
    fderiv ℝ (fun x : D => psi (z.1,observer.symm x)) z.2 =
      (fderiv ℝ (fun x : D => psi (z.1,owner.symm x)) (owner (observer.symm z.2))).comp
        (actualJointSpatialJacobian (repairReferenceHostTransition observer owner) z) := by
  let b := repairReferenceHostTransition (Ep := Ep) observer owner
  let f : D → ℝ := fun x => psi (z.1,owner.symm x)
  let t : D → D := owner ∘ observer.symm
  have ht : DifferentiableAt ℝ t z.2 := by
    have h := ((repair_reference_host_transition_smooth (Ep := Ep) observer owner hObserver hOwner).1.snd
      |>.contDiffAt (b.open_source.mem_nhds hz)).comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
    exact h.differentiableAt (by simp)
  have he : (fun x : D => psi (z.1,observer.symm x)) =ᶠ[𝓝 z.2] f ∘ t := by
    filter_upwards [(b.open_source.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz] with x hx
    change psi (z.1,observer.symm x) = psi (z.1,owner.symm (owner (observer.symm x)))
    have hxo : observer.symm x ∈ owner.source := hx.2.2
    rw [owner.left_inv hxo]
  rw [he.fderiv_eq,fderiv_comp z.2 hPhase ht]
  rfl

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

theorem increment_actual_signed_observing_host_reserves
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 < T)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (observer owner : OpenPartialHomeomorph M D)
    (hObserver : observer ∈ IsManifold.maximalAtlas I ∞ M)
    (hOwner : owner ∈ IsManifold.maximalAtlas I ∞ M)
    (W : Set X) (hW : IsOpen W)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (owner.symm z.2)) W)
    (psi : Ep × M → ℝ) (z : X)
    (hz : z ∈ (repairReferenceHostTransition observer owner).source)
    (hzw : repairReferenceHostTransition observer owner z ∈ W)
    (hPhase : DifferentiableAt ℝ (fun x : D => psi (z.1,owner.symm x)) (owner (observer.symm z.2)))
    (hInverse : ‖fderiv ℝ (observer ∘ owner.symm) (owner (observer.symm z.2))‖ ≤ T)
    (i : C.indices) (a : EdgePair (Module.finrank ℝ D+1))
    (hUpper : ‖round4ActualPhaseOperatorInChart F (fun _ => owner)
      (repairReferenceHostTransition observer owner z)‖ ≤ R)
    (hTemplate : round4ActualPhaseOperatorInChart F (fun _ => owner)
      (repairReferenceHostTransition observer owner z) ∈ (C.template i).operatorDomain)
    (weight : ℝ) (hWeight : 1 ≤ |weight|)
    (hClose : ‖weight⁻¹ • fderiv ℝ (fun x : D => psi (z.1,owner.symm x))
      (owner (observer.symm z.2)) - (C.template i).covectors a‖ < incrementUniformSignedRadius C R) :
    (C.covectorRadius/2)/T ≤ ‖fderiv ℝ (fun x : D => psi (z.1,observer.symm x)) z.2‖ ∧
    ∀ v, (incrementUniformSignedMargin C R/T^2)*‖v‖ ≤
      ‖covectorRestriction (round4ActualPhaseOperatorInChart F (fun _ => observer) z)
        (fderiv ℝ (fun x : D => psi (z.1,observer.symm x)) z.2) v‖ := by
  let b := repairReferenceHostTransition (Ep := Ep) observer owner
  let U := b.source ∩ b ⁻¹' W
  have hU : IsOpen U := b.isOpen_inter_preimage hW
  have ht := repair_reference_host_transition_smooth (Ep := Ep) observer owner hObserver hOwner
  obtain ⟨A,hA,hAi⟩ := repair_reference_transition_spatial_equiv observer owner hObserver hOwner z hz
  have hOperator := repair_reference_actual_phase_operator_transport F hF
    (fun _ => owner) (fun _ => observer) (fun _ => hOwner) U W hU hW hJoint
    (ht.1.mono inter_subset_left) (fun _ hy => hy.2) (fun _ hy => hy.1.2) z ⟨hz,hzw⟩
  have hCovector := increment_actual_phase_covector_transport observer owner hObserver hOwner psi z hz hPhase
  have hJ : actualJointSpatialJacobian (actualSourceChartTransition
      (fun _ => owner) (fun _ => observer)) z = A.toContinuousLinearMap := hA.symm
  have hCovector' : fderiv ℝ (fun x : D => psi (z.1,observer.symm x)) z.2 =
      (fderiv ℝ (fun x : D => psi (z.1,owner.symm x)) (owner (observer.symm z.2))).comp
        A.toContinuousLinearMap := by
    rw [hA]
    exact hCovector
  have hNorm := increment_normalized_signed_norm_lower C R i a _ weight hWeight hClose
  have hWeight0 : weight ≠ 0 := by
    intro h
    subst weight
    norm_num at hWeight
  have hKernel := (increment_uniform_signed_control C R
    (round4ActualPhaseOperatorInChart F (fun _ => owner) (b z)) hUpper i hTemplate a
    (fderiv ℝ (fun x : D => psi (z.1,owner.symm x)) (owner (observer.symm z.2)))
    weight hWeight0 hClose).2.1
  constructor
  · rw [hCovector']
    exact increment_covector_transition_norm_lower A _ _ T hT (by rwa [hAi]) hNorm
  · rw [hOperator,hCovector',hJ]
    exact repair_reference_kernel_lower_transport A _ _ (incrementUniformSignedMargin C R) T
      (incrementUniformSignedMargin_pos C R).le hT (by rwa [hAi]) hKernel

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_phase_covector_transport
#print axioms GlobalEmbedding.Continuation.increment_actual_signed_observing_host_reserves
