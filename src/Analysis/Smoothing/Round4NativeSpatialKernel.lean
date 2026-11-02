import Probes.ActualSecondaryInverseTensor
import Probes.ActualIncrementHostGeometryInputs
import Probes.ActualIncrementKernelCoordinates

/-! The inverse of a genuine parameter-preserving joint chart gives a
Euclidean spatial equivalence. Its kernel covector is the SAME original
linear phase, and its inverse norm is bounded by the joint forward norm.
No norm on a manifold tangent fibre enters this construction. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round4_actual_native_spatial_equiv
    (b : OpenPartialHomeomorph X X)
    (hb : ContDiffOn ℝ ∞ b b.source) (hbi : ContDiffOn ℝ ∞ b.symm b.target)
    (hp : ∀ y ∈ b.source, (b y).1 = y.1)
    (hpi : ∀ z ∈ b.target, (b.symm z).1 = z.1)
    (xi : D →L[ℝ] ℝ) (hphase : ∀ y ∈ b.source, (b y).2 0 = xi y.2)
    (B : ℝ) (hB : ∀ y ∈ b.source, ‖fderiv ℝ b y‖ ≤ B)
    (z : X) (hz : z ∈ b.target) :
    ∃ A : D ≃L[ℝ] D,
      A.toContinuousLinearMap = actualJointSpatialJacobian b.symm z ∧
      A.symm.toContinuousLinearMap = actualJointSpatialJacobian b (b.symm z) ∧
      actualIncrementCoordinateCovector A = xi ∧
      ‖A.symm.toContinuousLinearMap‖ ≤ B := by
  let J := actualJointSpatialJacobian b.symm z
  let S := actualJointSpatialJacobian b (b.symm z)
  have hSJ : S.comp J = ContinuousLinearMap.id ℝ D :=
    actual_joint_spatial_jacobian_inverse b.symm hbi hb hpi z hz
  have hJS : J.comp S = ContinuousLinearMap.id ℝ D := by
    have h := actual_joint_spatial_jacobian_inverse b hb hbi hp (b.symm z) (b.map_target hz)
    simpa only [b.right_inv hz] using h
  let A := ContinuousLinearEquiv.equivOfInverse J S
    (fun v => congrArg (fun L : D →L[ℝ] D => L v) hSJ)
    (fun v => congrArg (fun L : D →L[ℝ] D => L v) hJS)
  refine ⟨A, rfl, rfl, ?_, ?_⟩
  · let y := b.symm z
    let f : D → D := fun x => (b (y.1,x)).2
    have hy : y ∈ b.source := b.map_target hz
    have hf : DifferentiableAt ℝ f y.2 :=
      ((hb.contDiffAt (b.open_source.mem_nhds hy)).snd.comp y.2
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hg : (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (m+1)) 0) ∘ f =ᶠ[𝓝 y.2] xi := by
      filter_upwards [(b.open_source.preimage (continuous_const.prodMk continuous_id)).mem_nhds hy]
        with x hx
      exact hphase (y.1,x) hx
    have hd := hg.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp y.2 (EuclideanSpace.proj 0).differentiableAt hf,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv] at hd
    exact hd
  · exact (actual_joint_spatial_jacobian_norm_le b b.source b.open_source hb
      (b.symm z) (b.map_target hz)).trans (hB _ (b.map_target hz))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_native_spatial_equiv
