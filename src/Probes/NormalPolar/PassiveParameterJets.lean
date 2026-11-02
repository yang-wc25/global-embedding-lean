import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The actual jets of a passive parameter extension

Adding a passive normed parameter to a one-point seed does not change the
operator norm of any actual joint derivative.  This is proved on the real
open domain of the seed, using the actual continuous linear projection and
its contractive right inverse.  In particular, all seed raw derivative
profiles transfer with the same constants; no completed-wave estimate is
assumed and no equivalence of norms is introduced.
-/

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {S E D V : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The real linear map used by the passive parameter extension. -/
def passiveParameterProjection : (E × D) →L[ℝ] (S × D) :=
  (0 : (E × D) →L[ℝ] S).prod (ContinuousLinearMap.snd ℝ E D)

@[simp] theorem passiveParameterProjection_apply (z : E × D) :
    passiveParameterProjection (S := S) z = (0,z.2) := rfl

theorem passiveParameterProjection_norm_le_one :
    ‖passiveParameterProjection (S := S) (E := E) (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [passiveParameterProjection_apply, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg _), one_mul] using le_max_right ‖z.1‖ ‖z.2‖

theorem passiveParameterProjection_multilinear_norm_le {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => S × D) V) :
    ‖A.compContinuousLinearMap (fun _ => passiveParameterProjection (E := E))‖ ≤ ‖A‖ := by
  apply (A.norm_compContinuousLinearMap_le _).trans
  have hp : (∏ _ : Fin j, ‖passiveParameterProjection (S := S) (E := E) (D := D)‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun _ _ => passiveParameterProjection_norm_le_one)
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg A)).trans_eq (mul_one _)

variable [Subsingleton S]

/-- The inverse insertion proves exact norm preservation, including order
zero and a zero-dimensional spatial domain. -/
theorem passiveParameterProjection_multilinear_norm_eq {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => S × D) V) :
    ‖A.compContinuousLinearMap (fun _ => passiveParameterProjection (E := E))‖ = ‖A‖ := by
  apply le_antisymm (passiveParameterProjection_multilinear_norm_le A)
  have hback :
      (A.compContinuousLinearMap (fun _ => passiveParameterProjection (E := E))).compContinuousLinearMap
        (fun _ => passiveParameterProjection (S := E) (E := S) (D := D)) = A := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      passiveParameterProjection_apply]
    congr 1
    funext i
    exact Prod.ext (Subsingleton.elim _ _) rfl
  calc
    ‖A‖ = ‖(A.compContinuousLinearMap (fun _ => passiveParameterProjection (E := E))).compContinuousLinearMap
        (fun _ => passiveParameterProjection (S := E) (E := S) (D := D))‖ := congrArg norm hback.symm
    _ ≤ ‖A.compContinuousLinearMap (fun _ => passiveParameterProjection (E := E))‖ :=
      passiveParameterProjection_multilinear_norm_le _

/-- Actual joint derivatives on the exact lifted open domain.  Smoothness is
only required on the seed domain, rather than on an artificial extension. -/
theorem passiveParameter_iteratedFDeriv {n : ℕ∞ω} (s₀ : S) (f : S × D → V)
    (O : Set (S × D)) (hO : IsOpen O) (hf : ContDiffOn ℝ n f O)
    (z : E × D) (hz : (s₀,z.2) ∈ O) (j : ℕ) (hj : (j : ℕ∞ω) ≤ n) :
    iteratedFDeriv ℝ j (fun w : E × D => f (s₀,w.2)) z =
      (iteratedFDeriv ℝ j f (s₀,z.2)).compContinuousLinearMap
        (fun _ => passiveParameterProjection (E := E)) := by
  have hs : s₀ = 0 := Subsingleton.elim _ _
  subst s₀
  let L : (E × D) →L[ℝ] (S × D) := passiveParameterProjection
  have hzL : L z ∈ O := hz
  have hpre : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have hp := L.iteratedFDerivWithin_comp_right hf hO.uniqueDiffOn hpre.uniqueDiffOn hzL hj
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
      (((hf.comp_continuousLinearMap L).contDiffAt (hpre.mem_nhds hzL)).of_le hj) hzL,
    iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
      ((hf.contDiffAt (hO.mem_nhds hzL)).of_le hj) hzL] at hp
  exact hp

/-- The full joint derivative norm equals the seed norm without any
dimension-dependent factor or change of the product norm. -/
theorem passiveParameter_iteratedFDeriv_norm {n : ℕ∞ω} (s₀ : S) (f : S × D → V)
    (O : Set (S × D)) (hO : IsOpen O) (hf : ContDiffOn ℝ n f O)
    (z : E × D) (hz : (s₀,z.2) ∈ O) (j : ℕ) (hj : (j : ℕ∞ω) ≤ n) :
    ‖iteratedFDeriv ℝ j (fun w : E × D => f (s₀,w.2)) z‖ =
      ‖iteratedFDeriv ℝ j f (s₀,z.2)‖ := by
  rw [passiveParameter_iteratedFDeriv s₀ f O hO hf z hz j hj]
  exact passiveParameterProjection_multilinear_norm_eq _

/-- Every raw derivative profile transfers to the full joint parameter
domain with its original budget. -/
theorem passiveParameter_raw_profile {n : ℕ∞ω} (s₀ : S) (f : S × D → V)
    (O : Set (S × D)) (hO : IsOpen O) (hf : ContDiffOn ℝ n f O)
    (W : ℕ → S × D → ℝ)
    (hW : ∀ j : ℕ, (j : ℕ∞ω) ≤ n → ∀ w ∈ O, ‖iteratedFDeriv ℝ j f w‖ ≤ W j w) :
    ∀ j : ℕ, (j : ℕ∞ω) ≤ n → ∀ z : E × D, (s₀,z.2) ∈ O →
      ‖iteratedFDeriv ℝ j (fun w : E × D => f (s₀,w.2)) z‖ ≤ W j (s₀,z.2) := by
  intro j hj z hz
  rw [passiveParameter_iteratedFDeriv_norm s₀ f O hO hf z hz j hj]
  exact hW j hj (s₀,z.2) hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameterProjection_multilinear_norm_eq
#print axioms GlobalEmbedding.Continuation.passiveParameter_iteratedFDeriv_norm
#print axioms GlobalEmbedding.Continuation.passiveParameter_raw_profile
