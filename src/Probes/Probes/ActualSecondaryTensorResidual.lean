import Probes.ActualSecondaryRemodulation
import Probes.ActualJointTensorChartTransfer
import Smoothing.ParameterRound2MeanTensorAlgebra

/-!
# Actual real residual tensors and their genuine frame transport

The original complex physical residual is remodulated before taking its real
tensor. The fixed coefficient assembly preserves every ordered basis entry.
The subsequent transport inserts the true spatial Jacobian twice. Thus this
consumer estimates an actual bilinear tensor in the observation chart, not
an array of untransported adapted-chart components.
-/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "CMatrix" => Fin (m + 1) → Fin (m + 1) → ℂ

private local instance residualTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance residualTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance residualTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def actualComplexTensorUncurry : CMatrix →L[ℝ] ((Fin (m + 1) × Fin (m + 1)) → ℂ) :=
  ContinuousLinearMap.pi fun ij =>
    (ContinuousLinearMap.proj ij.2 : (Fin (m + 1) → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj ij.1 : CMatrix →L[ℝ] (Fin (m + 1) → ℂ))

@[simp] theorem actualComplexTensorUncurry_apply (a : CMatrix) (i j : Fin (m + 1)) :
    actualComplexTensorUncurry a (i,j) = a i j := rfl

theorem actualComplexTensorUncurry_norm_le : ‖actualComplexTensorUncurry (m := m)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
  intro ij
  exact (norm_le_pi_norm (a ij.1) ij.2).trans (norm_le_pi_norm a ij.1)

/-- Fixed native assembly, using the SAME real tensor assembly as the original mean. -/
def actualRealTensorAssembly : CMatrix →L[ℝ] (D →L[ℝ] D →L[ℝ] ℝ) :=
  (parameterRound2_meanTensorAssembly (m+1)).comp actualComplexTensorUncurry

theorem actualRealTensorAssembly_basis (a : CMatrix) (i j : Fin (m + 1)) :
    actualRealTensorAssembly a (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      (a i j).re :=
  parameterRound2_meanTensorAssembly_basis (m+1) (actualComplexTensorUncurry a) i j

theorem actualRealTensorAssembly_norm_le : ‖actualRealTensorAssembly (m := m)‖ ≤
    ‖parameterRound2_meanTensorAssembly (m+1)‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) actualComplexTensorUncurry_norm_le)

section Remodulation
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def actualRemodulatedPhysicalTensor (e : X → CMatrix) (phase : X → ℝ) (tau : ℝ) :
    X → D →L[ℝ] D →L[ℝ] ℝ :=
  fun z => actualRealTensorAssembly
    (fun i j => Complex.exp (((phase z / tau : ℝ) : ℂ) * Complex.I) * e z i j)

theorem actualRemodulatedPhysicalTensor_basis (e : X → CMatrix) (phase : X → ℝ)
    (tau : ℝ) (z : X) (i j : Fin (m + 1)) :
    actualRemodulatedPhysicalTensor e phase tau z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      (Complex.exp (((phase z / tau : ℝ) : ℂ) * Complex.I) * e z i j).re :=
  actualRealTensorAssembly_basis _ i j

theorem actual_remodulated_physical_tensor_weighted_jets
    (e : X → CMatrix) (phase : X → ℝ) (O S : Set X)
    (hO : IsOpen O) (hSO : S ⊆ O) (he : ContDiffOn ℝ ∞ e O)
    (hphase : ContDiffOn ℝ ∞ phase O) (j : ℕ) (tau ell M K : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K)
    (hp : ∀ k < j, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ (k+1) phase z‖ ≤ M)
    (heb : ∀ k ≤ j, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k e z‖ ≤ K) :
    ContDiffOn ℝ ∞ (actualRemodulatedPhysicalTensor e phase tau) O ∧
      ∀ r ≤ j, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r
        (actualRemodulatedPhysicalTensor e phase tau) z‖ ≤
        ‖parameterRound2_meanTensorAssembly (m+1)‖ * incrementsFastMultiplierConstant j M * K := by
  let W := fun z => Complex.exp (Complex.I * ((phase z / tau : ℝ) : ℂ)) • e z
  have hW : ContDiffOn ℝ ∞ W O :=
    (increments_fast_phase_contDiffOn O phase hphase tau).smul he
  have heq : actualRemodulatedPhysicalTensor e phase tau = actualRealTensorAssembly ∘ W := by
    funext z
    unfold actualRemodulatedPhysicalTensor
    simp only [Function.comp_apply]
    apply congrArg actualRealTensorAssembly
    funext i a
    simp only [W, Pi.smul_apply, smul_eq_mul, mul_comm Complex.I]
  rw [heq]
  refine ⟨actualRealTensorAssembly.contDiff.comp_contDiffOn hW, ?_⟩
  intro r hr z hz
  have hb := increments_fast_multiplier_jet_bound j r hr O hO phase e hphase he z (hSO hz)
    tau ell M K htau htaul hell1 hK (fun k hk => hp k hk z hz) (fun k hk => heb k hk z hz)
  have hnonneg : 0 ≤ incrementsFastMultiplierConstant j M * K :=
    mul_nonneg (incrementsFastMultiplierConstant_pos j M).le hK
  have h := (slow_linear_jet_bound actualRealTensorAssembly O hO W hW r tau
    (incrementsFastMultiplierConstant j M * K) htau.le z (hSO hz) hb).trans
      (mul_le_mul_of_nonneg_right actualRealTensorAssembly_norm_le hnonneg)
  exact h.trans_eq (by ring)

end Remodulation

section Transport
variable {Ep Es Eq : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]

theorem actual_remodulated_physical_tensor_chart_jets
    (e : Eq × D → CMatrix) (phase : Eq × D → ℝ)
    (phi : Ep × Es → Eq × D) (O S : Set (Eq × D)) (U : Set (Ep × Es))
    (hO : IsOpen O) (hSO : S ⊆ O) (hU : IsOpen U)
    (he : ContDiffOn ℝ ∞ e O) (hphase : ContDiffOn ℝ ∞ phase O)
    (hphi : ContDiffOn ℝ ∞ phi U) (hmap : MapsTo phi U O)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) (tau ell M K : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hK : 0 ≤ K)
    (hp : ∀ k < j, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ (k+1) phase z‖ ≤ M)
    (heb : ∀ k ≤ j, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k e z‖ ≤ K)
    (z : Ep × Es) (hz : z ∈ U) (hzS : phi z ∈ S)
    (hphijet : ∀ i, 1 ≤ i → i ≤ j+1 →
      ell ^ (i-1) * ‖iteratedFDeriv ℝ i phi z‖ ≤ T i) :
    let B := actualRemodulatedPhysicalTensor e phase tau
    ContDiffOn ℝ ∞ (fun y => (B (phi y)).bilinearComp
      (actualJointSpatialJacobian phi y) (actualJointSpatialJacobian phi y)) U ∧
    tau ^ j * ‖iteratedFDeriv ℝ j (fun y => (B (phi y)).bilinearComp
      (actualJointSpatialJacobian phi y) (actualJointSpatialJacobian phi y)) z‖ ≤
      actualFastTensorChartTransferCost T j * ‖parameterRound2_meanTensorAssembly (m+1)‖ *
        incrementsFastMultiplierConstant j M * K := by
  intro B
  obtain ⟨hB, hb⟩ := actual_remodulated_physical_tensor_weighted_jets e phase O S hO hSO he hphase
    j tau ell M K htau htaul hell1 hK hp heb
  have hC : 0 ≤ ‖parameterRound2_meanTensorAssembly (m+1)‖ * incrementsFastMultiplierConstant j M * K :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (incrementsFastMultiplierConstant_pos j M).le) hK
  obtain ⟨hc, hbound⟩ := actual_fast_joint_tensor_chart_transfer T hT j phi B U O hU hO hphi hB hmap
    z hz tau ell (‖parameterRound2_meanTensorAssembly (m+1)‖ * incrementsFastMultiplierConstant j M * K)
    htau htaul hC (fun i hi => hb i hi _ hzS) hphijet
  exact ⟨hc, hbound.trans_eq (by ring)⟩

end Transport
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualRealTensorAssembly_basis
#print axioms GlobalEmbedding.Continuation.actual_remodulated_physical_tensor_weighted_jets
#print axioms GlobalEmbedding.Continuation.actual_remodulated_physical_tensor_chart_jets
