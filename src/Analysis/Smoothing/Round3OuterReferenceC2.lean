import Smoothing.ParameterRound2NormAlgebra
import GlobalEmbedding.Offline.PaperSmoothingEstimates

/-! The same smoothing defect and inherited map displacement control SF-F0
in the unchanged original C2 norm. The estimate uses the atlas maximum and
adds no chart-count factor. All real projections retain finite guards. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {ι : Type*} [Fintype ι] {n q : ℕ}

theorem round3_original_reference_C2_from_tail
    (u SF F0 : ι → (Fin n → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (O i))
    (hSF : ∀ i, ContDiffOn ℝ ∞ (SF i) (O i))
    (hF0 : ∀ i, ContDiffOn ℝ ∞ (F0 i) (O i))
    (hTailFinite : paperAtlasCj 2 (fun i y => u i y-SF i y) O S ≠ ⊤)
    (hOldFinite : paperAtlasCj 2 (fun i y => u i y-F0 i y) O S ≠ ⊤)
    (tail inherited : ℝ)
    (hTail : (paperAtlasCj 2 (fun i y => u i y-SF i y) O S).toReal ≤ tail)
    (hOld : (paperAtlasCj 2 (fun i y => u i y-F0 i y) O S).toReal ≤ inherited) :
    paperAtlasCj 2 (fun i y => SF i y-F0 i y) O S ≠ ⊤ ∧
    (paperAtlasCj 2 (fun i y => SF i y-F0 i y) O S).toReal ≤ tail+inherited := by
  have hneg := paperAtlasCj_neg 2 (fun i y => u i y-SF i y) O S hO hSO
    (fun i => (hu i).sub (hSF i))
  change paperAtlasCj 2 (fun i y => -(u i y-SF i y)) O S =
    paperAtlasCj 2 (fun i y => u i y-SF i y) O S at hneg
  have hnFinite : paperAtlasCj 2 (fun i y => -(u i y-SF i y)) O S ≠ ⊤ := by
    exact hneg.trans_ne hTailFinite
  have hadd := parameterRound2_paperAtlasCj_add_le 2
    (fun i y => -(u i y-SF i y)) (fun i y => u i y-F0 i y) O S hO hSO
    (fun i => ((hu i).sub (hSF i)).neg) (fun i => (hu i).sub (hF0 i)) hnFinite hOldFinite
  have heq : (fun i y => -(u i y-SF i y)+(u i y-F0 i y)) =
      (fun i y => SF i y-F0 i y) := by funext i y; abel
  rw [heq,hneg] at hadd
  have hs := ENNReal.add_ne_top.mpr ⟨hTailFinite,hOldFinite⟩
  refine ⟨ne_top_of_le_ne_top hs hadd,?_⟩
  have hreal := ENNReal.toReal_mono hs hadd
  rw [ENNReal.toReal_add hTailFinite hOldFinite] at hreal
  exact hreal.trans (add_le_add hTail hOld)

#print axioms round3_original_reference_C2_from_tail
end GlobalEmbedding.Continuation
