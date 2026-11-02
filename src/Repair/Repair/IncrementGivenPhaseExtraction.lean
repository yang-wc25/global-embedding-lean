import Probes.ActualOriginalPhaseProfileJets
import Probes.ActualOriginalTransitionProfileJets
import Smoothing.ParameterRound2WeightedJetNorms

/-! Fixed continuous linear coordinate extractions from actual first
 derivatives. Their j-th joint jets read exactly the (j+1)-st derivative
 of the original scalar phase or original transition. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def incrementGivenTotalExtraction (a : ℕ) :
    ((Fin a → ℝ) →L[ℝ] ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi fun r => ContinuousLinearMap.apply ℝ ℝ (Pi.single r 1)

def incrementGivenSpatialExtraction (n d : ℕ) :
    ((Fin (n+d) → ℝ) →L[ℝ] ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun r => ContinuousLinearMap.apply ℝ ℝ (Pi.single (Fin.castAdd d r) 1)

def incrementGivenTransitionExtraction (a : ℕ) :
    ((Fin a → ℝ) →L[ℝ] (Fin a → ℝ)) →L[ℝ] (Fin (a*a) → ℝ) :=
  ContinuousLinearMap.pi fun r =>
    (ContinuousLinearMap.proj (finProdFinEquiv.symm r).1 : (Fin a → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ (Fin a → ℝ) (Pi.single (finProdFinEquiv.symm r).2 1))

theorem increment_given_derivative_extraction_jets
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : (E →L[ℝ] F) →L[ℝ] G) (f : E → F) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) (B : ℝ)
    (hB : ‖iteratedFDeriv ℝ (j+1) f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (L ∘ fderiv ℝ f) x‖ ≤ ‖L‖*B := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hh := L.norm_iteratedFDeriv_comp_left hd (n := j) (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hB (norm_nonneg L))

theorem increment_given_positive_linear_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] ℝ) (f : E → F) (x : E) (hf : ContDiffAt ℝ ∞ f x)
    (weight cap bound B : ℝ) (hWeight : |weight| ≤ cap) (hCap : 0 ≤ cap)
    (hL : ‖L‖ ≤ bound) (hBound : 0 ≤ bound)
    (j : ℕ) (hB : ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => weight*L (f y)) x‖ ≤ cap*bound*B := by
  have hs := L.contDiff.contDiffAt.comp x hf
  change ‖iteratedFDeriv ℝ j (fun y => weight • ((L ∘ f) y)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hs.of_le (by simp)),norm_smul,Real.norm_eq_abs]
  have hh := L.norm_iteratedFDeriv_comp_left hf (n := j) (by simp)
  calc
    |weight| *‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ cap*‖iteratedFDeriv ℝ j (L ∘ f) x‖ :=
      mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
    _ ≤ cap*(‖L‖*‖iteratedFDeriv ℝ j f x‖) := mul_le_mul_of_nonneg_left hh hCap
    _ ≤ cap*(bound*B) := mul_le_mul_of_nonneg_left (mul_le_mul hL hB (norm_nonneg _) hBound) hCap
    _ = _ := by ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_given_derivative_extraction_jets
#print axioms GlobalEmbedding.Continuation.increment_given_positive_linear_jets
