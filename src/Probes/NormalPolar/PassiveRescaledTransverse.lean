import GlobalEmbedding.Paper.IncrementsModeAmbientTransverseFrame
import GlobalEmbedding.Offline.ImmersionRescaling

/-! Uniform transverse reserve for the same adapted slices under the
actual reference contraction. The entire original normal-column frame
scales by the same scalar; c >= 1/2 retains one quarter of its squared
ellipticity constant, before any c or probe parameter is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem passiveRescaled_secondForm_ambient
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (e : D → M) (x : D) (i j : Fin (m+1)) :
    (incrementsModeSecondForm (c • F) (contMDiff_const_rescale F hF c) e x i j : V) =
      c • (incrementsModeSecondForm F hF e x i j : V) :=
  DFunLike.congr_fun (trueSecondForm_const_rescale F hF c hc (e x))
    (symmetricSquareProduct (TangentSpace I (e x))
      (incrementsModeCoordinateDirections e x i) (incrementsModeCoordinateDirections e x j))

theorem passiveRescaled_transverse_frame
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (c : ℝ) (hc : c ≠ 0) (e : D → M) (x : D) :
    incrementsModeAmbientTransverseFrame (c • F) (contMDiff_const_rescale F hF c) e x =
      c • incrementsModeAmbientTransverseFrame F hF e x := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [incrementsModeAmbientTransverseFrame,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [passiveRescaled_secondForm_ambient F hF c hc e x]
  exact smul_comm _ _ _

theorem passiveRescaled_transverse_quarter_reserve
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (e : D → M) (x : D) (cT : ℝ)
    (hT : ∀ v : Tdata, cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame F hF e x v‖^2)
    (c : ℝ) (hc : 1/2 ≤ c) (v : Tdata) :
    (cT/4)*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (c • F) (contMDiff_const_rescale F hF c) e x v‖^2 := by
  have hc0 : 0 < c := by linarith
  rw [passiveRescaled_transverse_frame F hF c (ne_of_gt hc0),
    ContinuousLinearMap.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hc0]
  have hc2 : (1/4 : ℝ) ≤ c^2 := by nlinarith
  have hb := hT v
  have hscale := mul_le_mul_of_nonneg_right hc2
    (sq_nonneg ‖incrementsModeAmbientTransverseFrame F hF e x v‖)
  nlinarith

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRescaled_transverse_frame
#print axioms GlobalEmbedding.Continuation.passiveRescaled_transverse_quarter_reserve
