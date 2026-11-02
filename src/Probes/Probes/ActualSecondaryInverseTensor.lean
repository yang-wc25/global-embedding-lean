import Probes.ActualJointTensorChartTransfer
import Probes.ActualJointHomogeneousParameter

/-!
# True inverse spatial Jacobians and tensor pullback cancellation

For a genuine joint partial chart preserving parameters, the actual spatial
derivatives of the chart and its inverse compose to the identity. Therefore
the negative forcing may be pulled to an adapted chart and back without
changing the original tensor. Both frame factors are included explicitly.
-/

noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep Es Et Z : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem actual_joint_spatial_jacobian_inverse
    (e : OpenPartialHomeomorph (Ep × Es) (Ep × Et))
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target)
    (hfirst : ∀ y ∈ e.source, (e y).1 = y.1) (z : Ep × Es) (hz : z ∈ e.source) :
    (actualJointSpatialJacobian e.symm (e z)).comp (actualJointSpatialJacobian e z) =
      ContinuousLinearMap.id ℝ Es := by
  let phi : Es → Et := fun x => (e (z.1,x)).2
  let psi : Et → Es := fun x => (e.symm (z.1,x)).2
  have hphi : DifferentiableAt ℝ phi z.2 := by
    have hh : ContDiffOn ℝ ∞ phi ((fun x : Es => (z.1,x)) ⁻¹' e.source) :=
      he.snd.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx)
    exact (hh.contDiffAt ((e.open_source.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
  have hpsi : DifferentiableAt ℝ psi (phi z.2) := by
    have hh : ContDiffOn ℝ ∞ (fun x : Et => (e.symm ((e z).1,x)).2)
        ((fun x : Et => ((e z).1,x)) ⁻¹' e.target) :=
      hinv.snd.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx)
    have hmem : (e z).2 ∈ (fun x : Et => ((e z).1,x)) ⁻¹' e.target := e.map_source hz
    have hd := (hh.contDiffAt
      ((e.open_target.preimage (continuous_const.prodMk continuous_id)).mem_nhds hmem)).differentiableAt (by simp)
    simpa only [psi, phi, hfirst z hz] using hd
  have hcomp : psi ∘ phi =ᶠ[𝓝 z.2] id := by
    filter_upwards [(e.open_source.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz]
      with x hx
    have hh := congrArg Prod.snd (e.left_inv hx)
    dsimp only [id_eq] at hh
    have hpair : e (z.1,x) = (z.1, (e (z.1,x)).2) := Prod.ext (hfirst (z.1,x) hx) rfl
    rw [hpair] at hh
    exact hh
  have hder := hcomp.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp z.2 hpsi hphi, fderiv_id] at hder
  simpa only [actualJointSpatialJacobian, hfirst z hz, phi, psi] using hder

/-- Literal twice-covariant pullback by the inverse followed by the chart. -/
theorem actual_tensor_inverse_pullback_cancel
    (e : OpenPartialHomeomorph (Ep × Es) (Ep × Et))
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target)
    (hfirst : ∀ y ∈ e.source, (e y).1 = y.1)
    (B : Ep × Es → Es →L[ℝ] Es →L[ℝ] Z) (z : Ep × Es) (hz : z ∈ e.source) :
    ((B (e.symm (e z))).bilinearComp
      (actualJointSpatialJacobian e.symm (e z))
      (actualJointSpatialJacobian e.symm (e z))).bilinearComp
        (actualJointSpatialJacobian e z) (actualJointSpatialJacobian e z) = B z := by
  have hj := actual_joint_spatial_jacobian_inverse e he hinv hfirst z hz
  have hvec (v : Es) : actualJointSpatialJacobian e.symm (e z)
      (actualJointSpatialJacobian e z v) = v := by
    exact congrArg (fun A : Es →L[ℝ] Es => A v) hj
  rw [e.left_inv hz]
  ext v w
  simp only [ContinuousLinearMap.bilinearComp_apply, hvec]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_spatial_jacobian_inverse
#print axioms GlobalEmbedding.Continuation.actual_tensor_inverse_pullback_cancel
