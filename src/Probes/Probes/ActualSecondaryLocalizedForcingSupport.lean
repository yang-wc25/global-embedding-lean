import Probes.ActualSecondaryLocalizedForcingJets
import Probes.ActualSecondaryForcingPartition

/-! The genuine localized tensor forcing preserves its symmetry and actual
pair support. The support assertion is proved from zero germs through the
true inverse chart; pointwise zero values do not substitute for support. -/

noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_secondary_inverse_forcing_support
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor)
    (z : X) (hz : z ∈ e.target)
    (hs : z ∈ tsupport (actualSecondaryInverseForcing e cutoff H)) :
    e.symm z ∈ tsupport cutoff ∩ tsupport H := by
  have hinv : ContinuousAt e.symm z := e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hz)
  constructor
  · by_contra hnot
    have hzero := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto hinv
    have hh : actualSecondaryInverseForcing e cutoff H =ᶠ[𝓝 z] 0 := by
      filter_upwards [hzero] with y hy
      change actualTensorBasisCoefficients (cutoff (e.symm y) • _) = 0
      rw [show cutoff (e.symm y) = 0 from hy]
      ext i j
      simp only [actualTensorBasisCoefficients, smul_apply, smul_eq_mul, zero_mul, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hh) hs
  · by_contra hnot
    have hzero := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto hinv
    have hh : actualSecondaryInverseForcing e cutoff H =ᶠ[𝓝 z] 0 := by
      filter_upwards [hzero] with y hy
      change actualTensorBasisCoefficients (cutoff (e.symm y) • (H (e.symm y)).bilinearComp _ _) = 0
      rw [show H (e.symm y) = 0 from hy]
      ext i j
      simp only [actualTensorBasisCoefficients, smul_apply, ContinuousLinearMap.bilinearComp_apply,
        smul_eq_mul, zero_apply, mul_zero, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hh) hs

 theorem actual_secondary_inverse_forcing_symmetric
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor)
    (hH : ∀ y ∈ e.source, ∀ v w : D, H y v w = H y w v)
    (z : X) (hz : z ∈ e.target) (i j : Fin (m+1)) :
    actualSecondaryInverseForcing e cutoff H z i j = actualSecondaryInverseForcing e cutoff H z j i := by
  change cutoff (e.symm z) * H (e.symm z) _ _ = cutoff (e.symm z) * H (e.symm z) _ _
  rw [hH (e.symm z) (e.symm.map_source hz)]

 theorem actual_real_tensor_assembly_symmetric
    (H : Fin (m+1) → Fin (m+1) → ℂ) (hH : ∀ i j, H i j = H j i) (v w : D) :
    actualRealTensorAssembly H v w = actualRealTensorAssembly H w v := by
  have hh : actualRealTensorAssembly H = (actualRealTensorAssembly H).flip := by
    apply actual_bilinear_tensor_eq_of_basis
    intro i j
    change actualRealTensorAssembly H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      actualRealTensorAssembly H (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    simp only [actualRealTensorAssembly_basis, hH i j]
  exact congrArg (fun T : Tensor => T v w) hh

 theorem actual_imag_tensor_assembly_symmetric
    (H : Fin (m+1) → Fin (m+1) → ℂ) (hH : ∀ i j, H i j = H j i) (v w : D) :
    actualImaginaryTensorAssembly H v w = actualImaginaryTensorAssembly H w v := by
  apply actual_real_tensor_assembly_symmetric (fun i j => -Complex.I * H i j)
  intro i j
  rw [hH i j]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_inverse_forcing_support
#print axioms GlobalEmbedding.Continuation.actual_secondary_inverse_forcing_symmetric
