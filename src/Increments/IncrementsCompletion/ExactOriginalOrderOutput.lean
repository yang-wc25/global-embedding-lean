import Probes.Round3ParameterJointConclusion

/-!
# Exact original observation order and one common constant

The verified joint conclusion already controls one extra order of the same
increment.  This readout returns precisely order j as in (6.1), including
j = 0, by monotonicity of the unchanged original ENNReal weighted sum.  It
also uses one numerical C_j for both estimates.  Neither U nor any input,
norm, chart, domain, or threshold is changed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

theorem incrementsCompletion_original_weighted_order_mono
    {ι : Type*} [Fintype ι] {n a : ℕ}
    (base j k : ℕ) (tau : ℝ) (hjk : j ≤ k)
    (f : ι → (Fin n → ℝ) → Fin a → ℝ) (O S : ι → Set (Fin n → ℝ)) :
    paperAtlasWeighted base j tau f O S ≤ paperAtlasWeighted base k tau f O S := by
  unfold paperAtlasWeighted
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hjk))
  intro i hi hik
  positivity

variable {m d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem incrementsCompletion_exact_original_order_estimates
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (F U : P × M → V)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (q : ℕ) (delta tau ell : ℝ) (hdelta : 0 ≤ delta) (htau : 0 < tau) (hell : 0 < ell)
    (Cmap Cmetric : ℕ → ℝ) (hCmap : ∀ j, 0 ≤ Cmap j)
    (hOut : Round3ParameterJointIncrementConclusion A B S W F U H q delta tau ell Cmap Cmetric) :
    let C := fun j => max (Cmap j) (Cmetric j)
    ∀ j, 0 ≤ C j ∧
      paperAtlasWeighted 0 j tau (incrementsOriginalMapCoordinates A B U)
        (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalMapCoordinates A B U)
        (incrementsOriginalDifferentiation A B) S).toReal ≤ C j*delta*tau ∧
      paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
        (incrementsOriginalMetricError F U H delta)) (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
        (incrementsOriginalMetricError F U H delta)) (incrementsOriginalDifferentiation A B) S).toReal ≤
        C j*(delta*(tau/ell)^q+delta^3/tau) := by
  intro C j
  have hMap := hOut.map0 j
  have hMetric := hOut.metric j
  have hOrder := incrementsCompletion_original_weighted_order_mono 0 j (j+1) tau (by omega)
    (incrementsOriginalMapCoordinates A B U) (incrementsOriginalDifferentiation A B) S
  have hMapReal := ENNReal.toReal_mono hMap.1 hOrder
  have hMapCost : Cmap j*delta*tau ≤ C j*delta*tau :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hdelta) htau.le
  have hError : 0 ≤ delta*(tau/ell)^q+delta^3/tau := by positivity
  have hMetricCost : Cmetric j*(delta*(tau/ell)^q+delta^3/tau) ≤
      C j*(delta*(tau/ell)^q+delta^3/tau) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hError
  exact ⟨(hCmap j).trans (le_max_left _ _),ne_top_of_le_ne_top hMap.1 hOrder,
    hMapReal.trans (hMap.2.trans hMapCost),hMetric.1,hMetric.2.trans hMetricCost⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_weighted_order_mono
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_exact_original_order_estimates
