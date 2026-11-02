import Smoothing.ParameterRound2InitialCompact440
import GlobalEmbedding.Offline.RepairDisplacementBudget

/-! The actual repair initialization retains its initial C2 displacement.
The only map norm used here is the fixed reference C2 norm; the subsequent
440/442 entrance uses the existing original-coordinate initialization. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local instance round3InitialScalingChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3InitialScalingIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Literal square-root contraction in the original full-joint MAX norm.
In particular all parameter derivatives are included in this estimate. -/
theorem round3_repair_initial_scaling_original_bound
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (F0 : P × M → Ey) (hF0 : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F0)
    (j : ℕ) (delta : ℝ) :
    paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart
      (fun z => Real.sqrt (1-delta^2) • F0 z-F0 z))
      (incrementsOriginalDifferentiation A B.chart) S ≤
    ENNReal.ofReal (delta^2 *
      (paperAtlasCj j (incrementsOriginalMapCoordinates A B.chart F0)
        (incrementsOriginalDifferentiation A B.chart) S).toReal) := by
  let f := incrementsOriginalMapCoordinates A B.chart F0
  let O := incrementsOriginalDifferentiation A B.chart
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B.chart
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have hfinite := parameterRound2_paperAtlasCj_finite_of_compact f O S hO hS hSO hf j
  have heq : incrementsOriginalMapCoordinates A B.chart
      (fun z => Real.sqrt (1-delta^2) • F0 z-F0 z) =
      fun i y => (Real.sqrt (1-delta^2)-1) • f i y := by
    funext i y
    dsimp only [incrementsOriginalMapCoordinates, f]
    simpa only [sub_smul, one_smul] using
      (EuclideanSpace.equiv (Fin N) ℝ).map_smul
        (Real.sqrt (1-delta^2)-1) (F0 (incrementsOriginalJointPoint A B.chart i y))
  rw [heq]
  have h := parameterRound2_paperAtlasCj_smul_le j f O S hO hSO hf hfinite
    (Real.sqrt (1-delta^2)-1)
  calc
    _ ≤ ENNReal.ofReal |Real.sqrt (1-delta^2)-1| * paperAtlasCj j f O S := h
    _ = ENNReal.ofReal (|Real.sqrt (1-delta^2)-1| * (paperAtlasCj j f O S).toReal) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_toReal hfinite]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (initial_scaling_scalar_loss_le delta) ENNReal.toReal_nonneg)

/-- A preselected cap pays the initial scaling from the remaining C2
envelope of the actual closed repair state. -/
theorem round3_repair_initial_scaling_C2_envelope
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (F0 : P × M → Ey) (hF0 : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F0)
    {epsilon t : ℝ} (hepsilon : 0 < epsilon) (ht : 0 ≤ t) (htHalf : t ≤ 1/2)
    (hcap : t ≤ epsilon / (8 *
      ((paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart F0)
        (incrementsOriginalDifferentiation A B.chart) S).toReal+1))) :
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart
      (fun z => Real.sqrt (1-(t^10)^2) • F0 z-F0 z))
      (incrementsOriginalDifferentiation A B.chart) S).toReal ≤ (epsilon/4)*(1-t) := by
  let C := (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart F0)
    (incrementsOriginalDifferentiation A B.chart) S).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hnorm := round3_repair_initial_scaling_original_bound A B hA hB S hS hSO F0 hF0 2 (t^10)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) hC)] at hreal
  have ht1 : t ≤ 1 := htHalf.trans (by norm_num)
  have hpow : (t^10)^2 ≤ t := by
    rw [← pow_mul]
    simpa only [pow_one] using pow_le_pow_of_le_one ht ht1 (by omega : 1 ≤ 10*2)
  have hden : 0 < 8*(C+1) := by positivity
  have hpaid : t * C ≤ epsilon/8 := by
    have hh : t * (8*(C+1)) ≤ epsilon := (le_div_iff₀ hden).mp hcap
    nlinarith
  have hsmall : (t^10)^2*C ≤ epsilon/8 :=
    (mul_le_mul_of_nonneg_right hpow hC).trans hpaid
  change _ ≤ _ at hreal
  nlinarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_initial_scaling_original_bound
#print axioms GlobalEmbedding.Continuation.round3_repair_initial_scaling_C2_envelope
