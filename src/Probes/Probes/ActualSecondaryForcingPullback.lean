import Probes.ActualSecondaryInverseTensor
import Probes.ActualSecondaryPhysicalTensorEquality

/-!
# Literal negative-forcing localization and exact return to the original tensor

The local forcing is defined by the real inverse transition, both spatial
Jacobian factors and the actual subordinate cutoff. Remodulating in the true
adapted coordinate and returning to the observation chart gives exactly the
cutoff times the original modulated forcing. No tensor transformation identity
or reconstructed forcing is assumed as an input.
-/

noncomputable section
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ

def actualTensorBasisCoefficients (H : Tensor) : Source := fun i j =>
  H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem actual_local_forcing_tensor_eq_cos_sin
    (HR HI : X → Tensor) (tau : ℝ) (z : X) :
    actualSecondaryLocalForcingTensor (fun y => actualTensorBasisCoefficients (HR y))
      (fun y => actualTensorBasisCoefficients (HI y)) tau z =
      Real.cos (z.2 0 / tau) • HR z - Real.sin (z.2 0 / tau) • HI z := by
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  simp only [actualSecondaryLocalForcingTensor, actualRealTensorAssembly_basis,
    actualTensorBasisCoefficients, sub_apply, smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_add, add_zero,
    sub_self, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

def actualSecondaryInverseForcingTensor
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor) : X → Tensor :=
  fun z => cutoff (e.symm z) • (H (e.symm z)).bilinearComp
    (actualJointSpatialJacobian e.symm z) (actualJointSpatialJacobian e.symm z)

def actualSecondaryInverseForcing
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor) : X → Source :=
  fun z => actualTensorBasisCoefficients (actualSecondaryInverseForcingTensor e cutoff H z)

theorem actual_secondary_forcing_pullback_cancel
    (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target)
    (hfirst : ∀ y ∈ e.source, (e y).1 = y.1)
    (HR HI : X → Tensor) (cutoff phase : X → ℝ)
    (hadapted : ∀ y ∈ e.source, (e y).2 0 = phase y)
    (tau : ℝ) (z : X) (hz : z ∈ e.source) :
    (actualSecondaryLocalForcingTensor
      (actualSecondaryInverseForcing e cutoff HR) (actualSecondaryInverseForcing e cutoff HI)
      tau (e z)).bilinearComp
        (actualJointSpatialJacobian e z) (actualJointSpatialJacobian e z) =
      cutoff z • (Real.cos (phase z / tau) • HR z - Real.sin (phase z / tau) • HI z) := by
  have hj := actual_joint_spatial_jacobian_inverse e he hinv hfirst z hz
  have hvec (v : D) : actualJointSpatialJacobian e.symm (e z)
      (actualJointSpatialJacobian e z v) = v := by
    exact congrArg (fun A : D →L[ℝ] D => A v) hj
  change (actualSecondaryLocalForcingTensor
      (fun y => actualTensorBasisCoefficients (actualSecondaryInverseForcingTensor e cutoff HR y))
      (fun y => actualTensorBasisCoefficients (actualSecondaryInverseForcingTensor e cutoff HI y))
      tau (e z)).bilinearComp _ _ = _
  rw [actual_local_forcing_tensor_eq_cos_sin, hadapted z hz]
  unfold actualSecondaryInverseForcingTensor
  rw [e.left_inv hz]
  ext v w
  simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply, smul_apply, smul_eq_mul, hvec]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_local_forcing_tensor_eq_cos_sin
#print axioms GlobalEmbedding.Continuation.actual_secondary_forcing_pullback_cancel
