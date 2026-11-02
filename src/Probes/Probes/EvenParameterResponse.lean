import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic

/-!
# Even background parameters in the actual first probe step

Source: main.tex, proof of prop:probes immediately after (8.3).
The background response is O(norm u), because its derivative vanishes at zero
and its actual second derivative is bounded on the fixed parameter ball.
The estimates below use native Frechet derivatives, including an operator norm
bound uniform over every direction. No response estimate is a hypothesis.

The final recurrence lemma is conditional on evenness of its correction map;
it does not assert that the full geometric correction has been constructed.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Continuation

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuinely differentiable even map has zero actual derivative at zero. -/
theorem fderiv_zero_of_even {f : P → F} (heven : ∀ u, f (-u) = f u)
    (hf : DifferentiableAt ℝ f 0) : fderiv ℝ f 0 = 0 := by
  have hf' : HasFDerivAt f (fderiv ℝ f 0) (-(0 : P)) := by
    simpa only [neg_zero] using hf.hasFDerivAt
  have hcomp := hf'.comp (0 : P) (hasFDerivAt_id (0 : P)).neg
  have hder : (fderiv ℝ f 0).comp (-ContinuousLinearMap.id ℝ P) = fderiv ℝ f 0 := by
    have hc : HasFDerivAt f
        ((fderiv ℝ f 0).comp (-ContinuousLinearMap.id ℝ P)) 0 := by
      convert hcomp using 1
      funext u
      exact (heven u).symm
    exact hc.unique hf.hasFDerivAt
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg (fun L : P →L[ℝ] F ↦ L u) hder
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at hu
  have htwo : (2 : ℝ) • fderiv ℝ f 0 u = 0 := by
    calc
      (2 : ℝ) • fderiv ℝ f 0 u = fderiv ℝ f 0 u + fderiv ℝ f 0 u := two_smul _ _
      _ = -(fderiv ℝ f 0 u) + fderiv ℝ f 0 u := congrArg (fun z ↦ z + fderiv ℝ f 0 u) hu.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The true Hessian bound on a convex parameter domain gives the uniform
first-parameter response C * norm u. This includes the origin and zero directions. -/
theorem norm_fderiv_even_le {f : P → F} {S : Set P} {C : ℝ}
    (heven : ∀ u, f (-u) = f u) (h0 : (0 : P) ∈ S)
    (hS : Convex ℝ S)
    (hf : ∀ u ∈ S, DifferentiableAt ℝ f u)
    (hDf : ∀ u ∈ S, DifferentiableAt ℝ (fderiv ℝ f) u)
    (hDDf : ∀ u ∈ S, ‖fderiv ℝ (fderiv ℝ f) u‖ ≤ C)
    {u : P} (hu : u ∈ S) : ‖fderiv ℝ f u‖ ≤ C * ‖u‖ := by
  have h := hS.norm_image_sub_le_of_norm_fderiv_le hDf hDDf h0 hu
  simpa only [fderiv_zero_of_even heven (hf 0 h0), sub_zero] using h

/-- Directional response of the same even map, with no chosen derivative field. -/
theorem norm_fderiv_even_apply_le {f : P → F} {S : Set P} {C : ℝ}
    (heven : ∀ u, f (-u) = f u) (h0 : (0 : P) ∈ S)
    (hS : Convex ℝ S)
    (hf : ∀ u ∈ S, DifferentiableAt ℝ f u)
    (hDf : ∀ u ∈ S, DifferentiableAt ℝ (fderiv ℝ f) u)
    (hDDf : ∀ u ∈ S, ‖fderiv ℝ (fderiv ℝ f) u‖ ≤ C)
    {u : P} (hu : u ∈ S) (v : P) :
    ‖fderiv ℝ f u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  exact (fderiv ℝ f u).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_even_le heven h0 hS hf hDf hDDf hu) (norm_nonneg _))

/-- The literal finite mean substitutions from the first probe step. -/
def probeMeanSubstitution (target probe : P → F) (correction : F → P → F) :
    ℕ → P → F
  | 0 => target
  | j + 1 => fun u ↦ target u - probe u - correction (probeMeanSubstitution target probe correction j u) u

/-- Every actual finite substitution retains evenness once the actual mean
correction is known to be even in the probe parameters at each fixed background.
The statement retains this upstream hypothesis explicitly. -/
theorem probeMeanSubstitution_even (target probe : P → F) (correction : F → P → F)
    (htarget : ∀ u, target (-u) = target u)
    (hprobe : ∀ u, probe (-u) = probe u)
    (hcorrection : ∀ A u, correction A (-u) = correction A u) (j : ℕ) :
    ∀ u, probeMeanSubstitution target probe correction j (-u) =
      probeMeanSubstitution target probe correction j u := by
  induction j with
  | zero => exact htarget
  | succ j ih =>
    intro u
    simp only [probeMeanSubstitution, htarget, hprobe, ih, hcorrection]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fderiv_zero_of_even
#print axioms GlobalEmbedding.Continuation.norm_fderiv_even_le
#print axioms GlobalEmbedding.Continuation.norm_fderiv_even_apply_le
#print axioms GlobalEmbedding.Continuation.probeMeanSubstitution_even
