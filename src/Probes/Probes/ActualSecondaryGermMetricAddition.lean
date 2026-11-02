import Probes.ActualSecondaryOriginalRemainderCoordinates
import Smoothing.ParameterRound2TensorGermSpace

/-! The literal original metric error is added to its literal finite mean
residual in the actual original tensor germ space. Original norms, charts,
parameter coordinates and differentiation domains remain unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

 theorem actual_original_metric_error_norm_from_germ_remainder_and_mean
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F U : Ep × M → V)
    (H Mean : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (j q : ℕ) (delta tau ell CR CM : ℝ)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (htau : 0 < tau)
    (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hCR : 0 ≤ CR) (hCM : 0 ≤ CM)
    (hRest : incrementsOriginalMetricError F U Mean delta ∈ parameterRound2_originalTensorGermSpace A B S W)
    (hMean : (fun p x => delta^2 • (Mean p x-H p x)) ∈ parameterRound2_originalTensorGermSpace A B S W)
    (hRestBound : (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
      (incrementsOriginalMetricError F U Mean delta)) (incrementsOriginalDifferentiation A B) S).toReal ≤
      CR*(delta*(tau/ell)^q+delta^3/tau))
    (hMeanBound : (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
      (fun p x => delta^2 • (Mean p x-H p x))) (incrementsOriginalDifferentiation A B) S).toReal ≤
      CM*delta^2*(tau/ell)^(q+1)) :
    incrementsOriginalMetricError F U H delta ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
      (incrementsOriginalMetricError F U H delta)) (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
      (incrementsOriginalMetricError F U H delta)) (incrementsOriginalDifferentiation A B) S).toReal ≤
      (CR+CM)*(delta*(tau/ell)^q+delta^3/tau) := by
  let Rest : parameterRound2_originalTensorGermSpace A B S W := ⟨_,hRest⟩
  let MeanDefect : parameterRound2_originalTensorGermSpace A B S W := ⟨_,hMean⟩
  have heq : incrementsOriginalMetricError F U H delta = (Rest+MeanDefect).val := by
    funext p x
    change incrementsOriginalMetricError F U H delta p x =
      incrementsOriginalMetricError F U Mean delta p x+delta^2 • (Mean p x-H p x)
    ext v w
    simp only [incrementsOriginalMetricError,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    ring
  have hfinite := parameterRound2_tensorGerm_weighted_finite A B S W hS hSO (Rest+MeanDefect) 0 j tau
  have hs := map_add_le_add (parameterRound2_originalTensorGermSeminorm A B S W hS hSO tau j) Rest MeanDefect
  change (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B (Rest+MeanDefect).val)
    (incrementsOriginalDifferentiation A B) S).toReal ≤ _ at hs
  have hell : 0 < ell := htau.trans_le htaul
  have hd1 : delta ≤ 1 := hdeltatau.trans (htaul.trans hell1)
  have hratio : 0 ≤ tau/ell := div_nonneg htau.le hell.le
  have hratio1 : tau/ell ≤ 1 := (div_le_one hell).2 htaul
  have hmeanAbsorb : CM*delta^2*(tau/ell)^(q+1) ≤ CM*(delta*(tau/ell)^q+delta^3/tau) := by
    have hsquare : delta^2 ≤ delta := by nlinarith
    have hp : (tau/ell)^(q+1) ≤ (tau/ell)^q := pow_le_pow_of_le_one hratio hratio1 (by omega)
    calc
      _ ≤ CM*delta*(tau/ell)^q := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hCM (show 0 ≤ delta^3/tau by positivity)]
  refine ⟨?_,?_,?_⟩
  · rw [heq]
    exact (Rest+MeanDefect).property
  · rw [heq]
    exact hfinite
  · rw [heq]
    exact (hs.trans (add_le_add hRestBound (hMeanBound.trans hmeanAbsorb))).trans_eq (by ring)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_metric_error_norm_from_germ_remainder_and_mean
