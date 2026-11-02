import Probes.ActualSecondaryNativeTensorNorm
import Smoothing.ParameterRound2TensorGermSpace

/-! Native tensor jets on genuine sample neighborhoods give the unchanged
original atlas norm. The original differentiation domains are recovered by
actual open-germ restriction, without assuming regularity outside the true
open neighborhood or adding an atlas-cardinality constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d c : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance germNormTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance germNormTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance germNormTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_original_tensor_weighted_norm_from_native_germs
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (O : Fin A.count × Fin c → Set X) (hO : ∀ i, IsOpen (O i))
    (hOsub : ∀ i, O i ⊆ (B i.2).target ×ˢ (A.chart i.1).target)
    (hSO : ∀ i, (parameterTensorModelEquiv (m+1) d) ⁻¹' S i ⊆ O i)
    (Tfield : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (j : ℕ) (tau K : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hK : 0 ≤ K)
    (hE : ∀ i, ContDiffOn ℝ ∞ (actualOriginalNativeTargetTensor A B Tfield i) (O i))
    (hjet : ∀ i, ∀ k ≤ j, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (actualOriginalNativeTargetTensor A B Tfield i) z‖ ≤ K) :
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B Tfield i)
      ((parameterTensorModelEquiv (m+1) d).symm ⁻¹' O i)) ∧
    paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Tfield)
      (incrementsOriginalDifferentiation A B) S).toReal ≤
      (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*K := by
  let a := parameterTensorModelEquiv (m+1) d
  let S' := fun i => a ⁻¹' S i
  let EC := fun i => parameterRound2_metricComponents (m+1) ∘ actualOriginalNativeTargetTensor A B Tfield i
  have hEC (i) : ContDiffOn ℝ ∞ (EC i) (O i) :=
    (parameterRound2_metricComponents (m+1)).contDiff.comp_contDiffOn (hE i)
  have hECb : ∀ i, ∀ k ≤ j, ∀ z ∈ S' i, tau^k*‖iteratedFDeriv ℝ k (EC i) z‖ ≤ K := by
    intro i k hk z hz
    have h := slow_linear_jet_bound (parameterRound2_metricComponents (m+1)) (O i) (hO i)
      (actualOriginalNativeTargetTensor A B Tfield i) (hE i) k tau K htau.le z (hSO i hz)
      (hjet i k hk z hz)
    exact h.trans (mul_le_of_le_one_left hK (parameterRound2_metricComponents_norm_le (m+1)))
  have hreg (i) : ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B Tfield i) (a.symm ⁻¹' O i) := by
    apply ((hEC i).comp a.symm.contDiff.contDiffOn (fun y hy => hy)).congr
    exact fun y hy => actual_original_tensor_coordinates_native A B Tfield i y
  have hout := parameterRound2_paperAtlasWeighted_le_of_native_weighted_jets
    a j tau K htau htau1 hK EC O S' hO hSO hEC hECb
  have hSeq : modelCoordinateDomains a S' = S := by
    funext i
    ext y
    simp only [modelCoordinateDomains,S',Set.mem_preimage,a.apply_symm_apply]
  rw [hSeq] at hout
  have hSU : ∀ i, S i ⊆ modelCoordinateDomains a O i := by
    intro i y hy
    change a.symm y ∈ O i
    exact hSO i (by change a (a.symm y) ∈ S i; simpa only [a.apply_symm_apply] using hy)
  have hU : ∀ i, IsOpen (modelCoordinateDomains a O i) := fun i => (hO i).preimage a.symm.continuous
  have hUOrig : ∀ i, modelCoordinateDomains a O i ⊆ incrementsOriginalDifferentiation A B i := by
    intro i y hy
    have h := hOsub i hy
    exact ⟨h.2,h.1⟩
  have heqn := paperAtlasWeighted_congr_on 0 j tau (modelCoordinateDomains a O) S hSU
    (fun i y _ => actual_original_tensor_coordinates_native A B Tfield i y)
  have hrestrict := actual_paperAtlasWeighted_open_restrict 0 j tau
    (incrementsOriginalTensorCoordinates A B Tfield) (incrementsOriginalDifferentiation A B)
    (modelCoordinateDomains a O) S (parameterRound2_originalDifferentiation_open A B) hU hUOrig hSU
  refine ⟨hreg,?_⟩
  rw [hrestrict,heqn]
  exact hout

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_tensor_weighted_norm_from_native_germs
