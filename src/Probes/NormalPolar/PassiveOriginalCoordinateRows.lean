import NormalPolar.PassiveOriginalInjectedNorm
import Smoothing.ParameterSpatialPackets

/-! Original coordinate norms for selected actual matrix/covector rows.
Selecting a genuine coordinate or a zero row has cost one; joining the two
actual transition blocks costs at most the sum of their original norms.
All statements use literal scalar partials on the same domains. -/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

def passiveOriginalSelectRows {a q r : ℕ} (select : Fin r → Option (Fin q))
    (f : (Fin a → ℝ) → Fin q → ℝ) : (Fin a → ℝ) → Fin r → ℝ :=
  fun y c => match select c with
  | none => 0
  | some i => f y i

def passiveOriginalSelectTwoRows {a q p r : ℕ}
    (select : Fin r → Option (Fin q ⊕ Fin p))
    (f : (Fin a → ℝ) → Fin q → ℝ) (g : (Fin a → ℝ) → Fin p → ℝ) :
    (Fin a → ℝ) → Fin r → ℝ :=
  fun y c => match select c with
  | none => 0
  | some (.inl i) => f y i
  | some (.inr i) => g y i

theorem passiveOriginal_selectRows_norm_le {a q r : ℕ} (j : ℕ)
    (select : Fin r → Option (Fin q)) (f : (Fin a → ℝ) → Fin q → ℝ)
    (D T : Set (Fin a → ℝ)) :
    paperCoordinateCj j (passiveOriginalSelectRows select f) D T ≤ paperCoordinateCj j f D T := by
  unfold paperCoordinateCj
  refine iSup_le fun l => iSup_le fun y => iSup_le fun c => ?_
  cases h : select c with
  | none =>
    simp only [passiveOriginalSelectRows,h,passiveOriginal_partial_zero,norm_zero,ENNReal.ofReal_zero]
    exact bot_le
  | some i =>
    simp only [passiveOriginalSelectRows,h]
    exact le_iSup_of_le l (le_iSup_of_le y (le_iSup_of_le i le_rfl))

theorem passiveOriginal_selectTwoRows_norm_le {a q p r : ℕ} (j : ℕ)
    (select : Fin r → Option (Fin q ⊕ Fin p))
    (f : (Fin a → ℝ) → Fin q → ℝ) (g : (Fin a → ℝ) → Fin p → ℝ)
    (D T : Set (Fin a → ℝ)) :
    paperCoordinateCj j (passiveOriginalSelectTwoRows select f g) D T ≤
      paperCoordinateCj j f D T + paperCoordinateCj j g D T := by
  unfold paperCoordinateCj
  refine iSup_le fun l => iSup_le fun y => iSup_le fun c => ?_
  cases h : select c with
  | none =>
    simp only [passiveOriginalSelectTwoRows,h,passiveOriginal_partial_zero,norm_zero,ENNReal.ofReal_zero]
    exact bot_le
  | some i =>
    cases i with
    | inl i =>
      simp only [passiveOriginalSelectTwoRows,h]
      exact (passiveOriginal_partial_component_le j f D T l.val l.property.1 l.property.2
        y.val y.property i).trans (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from bot_le))
    | inr i =>
      simp only [passiveOriginalSelectTwoRows,h]
      exact (passiveOriginal_partial_component_le j g D T l.val l.property.1 l.property.2
        y.val y.property i).trans (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ _ from bot_le))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_selectRows_norm_le
#print axioms GlobalEmbedding.Continuation.passiveOriginal_selectTwoRows_norm_le
