import Probes.ActualSecondaryOriginalMetricCoordinates
import Smoothing.ParameterRound2RepairNormAlgebra
import Smoothing.ParameterRound2WeightedJetNorms

/-!
# The same actual metric error in the unchanged original atlas norm

Native full joint error jets are transferred to the literal original tensor
coordinates through the exact source-first model equivalence. Finiteness is
proved before taking toReal. Only the fixed model operator factor and the
original number of derivative levels appear, with no atlas cardinality.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {m d N pcount : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance originalNormTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance originalNormTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance originalNormTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_original_tensor_coordinates_native
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (Tfield : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (i : Fin A.count × Fin pcount) (y : Fin (m+1+d) → ℝ) :
    incrementsOriginalTensorCoordinates A B Tfield i y =
      parameterRound2_metricComponents (m+1)
        (actualOriginalNativeTargetTensor A B Tfield i ((parameterTensorModelEquiv (m+1) d).symm y)) := by
  funext k
  rw [parameterRound2_metricComponents_apply,actualOriginalNativeTargetTensor_basis]
  rfl

 theorem actual_original_tensor_weighted_norm_from_native
    (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin pcount → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (Tfield : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (j : ℕ) (tau C : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hC : 0 ≤ C)
    (hE : ∀ i, ContDiffOn ℝ ∞ (actualOriginalNativeTargetTensor A B Tfield i)
      ((B i.2).target ×ˢ (A.chart i.1).target))
    (hjet : ∀ i, ∀ k ≤ j, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k * ‖iteratedFDeriv ℝ k (actualOriginalNativeTargetTensor A B Tfield i) z‖ ≤ C) :
    let E := incrementsOriginalTensorCoordinates A B Tfield
    paperAtlasWeighted 0 j tau E (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau E (incrementsOriginalDifferentiation A B) S).toReal ≤
        (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*C := by
  intro E
  let a := parameterTensorModelEquiv (m+1) d
  let O := fun i : Fin A.count × Fin pcount => (B i.2).target ×ˢ (A.chart i.1).target
  let S' := fun i => a ⁻¹' S i
  let EC := fun i => parameterRound2_metricComponents (m+1) ∘ actualOriginalNativeTargetTensor A B Tfield i
  have hO : ∀ i, IsOpen (O i) := fun i => (B i.2).open_target.prod (A.chart i.1).open_target
  have hSO' : ∀ i, S' i ⊆ O i := by
    intro i z hz
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (a z), incrementsOriginalSourcePoint (a z)) = z :=
      a.symm_apply_apply z
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have hEC : ∀ i, ContDiffOn ℝ ∞ (EC i) (O i) := fun i =>
    (parameterRound2_metricComponents (m+1)).contDiff.comp_contDiffOn (hE i)
  have hECb : ∀ i, ∀ k ≤ j, ∀ z ∈ S' i, tau^k*‖iteratedFDeriv ℝ k (EC i) z‖ ≤ C := by
    intro i k hk z hz
    have h := slow_linear_jet_bound (parameterRound2_metricComponents (m+1)) (O i) (hO i)
      (actualOriginalNativeTargetTensor A B Tfield i) (hE i) k tau C htau.le z (hSO' i hz)
      (hjet i k hk z hz)
    exact h.trans (mul_le_of_le_one_left hC (parameterRound2_metricComponents_norm_le (m+1)))
  have hnorm := parameterRound2_paperAtlasWeighted_le_of_native_weighted_jets a j tau C htau htau1 hC
    EC O S' hO hSO' hEC hECb
  have hOeq : modelCoordinateDomains a O = incrementsOriginalDifferentiation A B := by
    funext i
    ext y
    change (incrementsOriginalParameterPoint y ∈ (B i.2).target ∧
      incrementsOriginalSourcePoint y ∈ (A.chart i.1).target) ↔ _
    exact and_comm
  have hSeq : modelCoordinateDomains a S' = S := by
    funext i
    ext y
    simp only [modelCoordinateDomains,S',Set.mem_preimage,a.apply_symm_apply]
  rw [hOeq,hSeq] at hnorm
  have heq : paperAtlasWeighted 0 j tau E (incrementsOriginalDifferentiation A B) S =
      paperAtlasWeighted 0 j tau (modelCoordinateFamily a EC) (incrementsOriginalDifferentiation A B) S := by
    apply paperAtlasWeighted_congr_on 0 j tau _ S hSO
    intro i y hy
    exact actual_original_tensor_coordinates_native A B Tfield i y
  rwa [← heq] at hnorm


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_tensor_coordinates_native
#print axioms GlobalEmbedding.Continuation.actual_original_tensor_weighted_norm_from_native
