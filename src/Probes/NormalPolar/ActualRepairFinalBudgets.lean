import NormalPolar.ActualRepairBudgetTransfer
import NormalPolar.ActualRepairModelModuli
import NormalPolar.ParameterDisplacementCenter

/-!
# Final original probe budgets from the actual first state and one repair tail

The first state's four original estimates and the already proved rates of
the same correction supply all four final estimates.  Constants are fixed
before the scale and parameters, and the entire original interval and ball
are retained.  This is the numerical assembly step used after the actual
same-run theorems; it does not postulate any final-map estimate.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

theorem actualRepairModelHessianModulus_product (C t : ℝ) (ht : 0 < t) :
    t ^ ((44 : ℝ) / 5) * actualRepairModelHessianModulus C t =
      2 * C * t ^ ((228 : ℝ) / 25) := by
  unfold actualRepairModelHessianModulus
  rw [abs_of_pos ht]
  calc
    _ = 2 * C * (t ^ ((44 : ℝ) / 5) * t ^ ((8 : ℝ) / 25)) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; norm_num

theorem actualRepairModelCOneModulus_product (C t : ℝ) (ht : 0 < t) :
    t ^ (10 : ℝ) * actualRepairModelCOneModulus C t =
      2 * C * t ^ ((264 : ℝ) / 25) := by
  unfold actualRepairModelCOneModulus
  rw [abs_of_pos ht]
  calc
    _ = 2 * C * (t ^ (10 : ℝ) * t ^ ((14 : ℝ) / 25)) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; norm_num

variable {n N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- The original final C2 displacement, C3 size, and both native parameter
budgets are consequences of the actual model and actual stronger tail.
The dimensional loss d comes only from converting true coordinate columns
to every direction in the original Pi norm. -/
theorem actual_repair_four_probe_budgets
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (F G : P → M → V) (radius threshold Cmodel Ctail : ℝ) (d : ℕ)
    (hCmodel : 0 ≤ Cmodel) (hCtail : 0 ≤ Ctail)
    (t : ℝ) (ht : 0 < t) (htt : t < threshold)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (Metric.ball 0 radius ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (Metric.ball 0 radius ×ˢ univ))
    (u : P) (hu : ‖u‖ < radius)
    (hclose : probeAtlasCj A 2 (G u - F₀) ≤
      ENNReal.ofReal (Cmodel * t ^ ((44 : ℝ) / 5)))
    (hthree : probeAtlasCj A 3 (G u) ≤ ENNReal.ofReal Cmodel)
    (hparamOne : ∀ v, probeAtlasCj A 1
      (fun x ↦ fderiv ℝ (fun w ↦ G w x) u v) ≤
        ENNReal.ofReal (Cmodel * t ^ (10 : ℕ) * ‖v‖))
    (hparamTwo : ∀ v, probeAtlasCj A 2
      (fun x ↦ fderiv ℝ (fun w ↦ G w x) u v) ≤
        ENNReal.ofReal (Cmodel * t ^ ((44 : ℝ) / 5) * ‖v‖))
    (htailTwo : probeAtlasCj A 2 (F u - G u) ≤
      ENNReal.ofReal (2 * Ctail * t ^ ((264 : ℝ) / 25)))
    (htailThree : probeAtlasCj A 3 (F u - G u) ≤
      ENNReal.ofReal (2 * Ctail * t ^ ((228 : ℝ) / 25)))
    (htailParamOne : ∀ v, probeAtlasCj A 1
      (fun x ↦ fderiv ℝ (fun w ↦ F w x - G w x) u v) ≤
        ENNReal.ofReal ((d : ℝ) * (2 * Ctail * t ^ ((264 : ℝ) / 25)) * ‖v‖))
    (htailParamTwo : ∀ v, probeAtlasCj A 2
      (fun x ↦ fderiv ℝ (fun w ↦ F w x - G w x) u v) ≤
        ENNReal.ofReal ((d : ℝ) * (2 * Ctail * t ^ ((228 : ℝ) / 25)) * ‖v‖)) :
    let C := actualRepairUniformBudget Cmodel Ctail threshold d
    probeAtlasCj A 2 (F u - F₀) ≤ ENNReal.ofReal (C * t ^ ((44 : ℝ) / 5)) ∧
    probeAtlasCj A 3 (F u) ≤ ENNReal.ofReal C ∧
    (∀ v, probeAtlasCj A 1 (fun x ↦ fderiv ℝ (fun w ↦ F w x) u v) ≤
      ENNReal.ofReal (C * t ^ (10 : ℕ) * ‖v‖)) ∧
    (∀ v, probeAtlasCj A 2 (fun x ↦ fderiv ℝ (fun w ↦ F w x) u v) ≤
      ENNReal.ofReal (C * t ^ ((44 : ℝ) / 5) * ‖v‖)) := by
  intro C
  have hfu := actualFamily_slice_smooth_of_joint F radius hF u hu
  have hgu := actualFamily_slice_smooth_of_joint G radius hG u hu
  have hub : u ∈ Metric.ball (0 : P) radius := by simpa using hu
  have hd : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hC := actualRepairUniformBudget_nonneg (threshold := threshold) hCmodel hCtail d
  have hscale (a b k : ℝ) (hk : 0 ≤ k) (hkd : k ≤ (d : ℝ) + 1)
      (hg : 0 ≤ a - b) (hgc : a - b ≤ (228 : ℝ) / 25) :
      Cmodel * t ^ b + k * (2 * Ctail * t ^ a) ≤ C * t ^ b :=
    actualRepairUniformBudget_absorbs Cmodel Ctail threshold d t a b k hCtail ht htt
      hk hkd hg hgc
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := probeAtlasCj_three_point_bound A hA 2 F₀ (G u) (F u)
      hF₀ hgu hfu (by positivity) (by positivity) hclose htailTwo
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa only [one_mul] using hscale ((264 : ℝ) / 25) ((44 : ℝ) / 5) 1
      (by norm_num) hd (by norm_num) (by norm_num)
  · have h := actual_repair_spatial_budget_of_model_tail A hA 3 (F u) (G u)
      hfu hgu hCmodel (by positivity) hthree htailThree
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa only [Real.rpow_zero, mul_one, one_mul] using
      hscale ((228 : ℝ) / 25) 0 1 (by norm_num) hd (by norm_num) (by norm_num)
  · intro v
    have h := actual_repair_parameter_budget_of_model_tail A hA hcover 1
      Metric.isOpen_ball F G hF hG u v hub (by positivity) (by positivity)
      (hparamOne v) (htailParamOne v)
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hs := mul_le_mul_of_nonneg_right
      (hscale ((264 : ℝ) / 25) 10 (d : ℝ) (by positivity) (by linarith)
        (by norm_num) (by norm_num)) (norm_nonneg v)
    have hten : t ^ (10 : ℝ) = t ^ (10 : ℕ) := by norm_num
    rw [hten] at hs
    simpa only [add_mul] using hs
  · intro v
    have h := actual_repair_parameter_budget_of_model_tail A hA hcover 2
      Metric.isOpen_ball F G hF hG u v hub (by positivity) (by positivity)
      (hparamTwo v) (htailParamTwo v)
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hs := mul_le_mul_of_nonneg_right
      (hscale ((228 : ℝ) / 25) ((44 : ℝ) / 5) (d : ℝ) (by positivity) (by linarith)
        (by norm_num) (by norm_num)) (norm_nonneg v)
    simpa only [add_mul] using hs

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actual_repair_four_probe_budgets
