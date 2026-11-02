import Smoothing.WeightedActualGram

/-!
# Native weighted bounds for fixed linear and bilinear operations

The norms of fixed coordinate conversions are retained explicitly. These
lemmas use the actual iterated derivative on an open local domain.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff

namespace GlobalEmbedding.Continuation

variable {D X Y Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem slow_linear_jet_bound (L : X →L[ℝ] Y)
    (O : Set D) (hO : IsOpen O) (f : D → X) (hf : ContDiffOn ℝ ∞ f O)
    (j : ℕ) (ell M : ℝ) (hell : 0 ≤ ell) (x : D) (hx : x ∈ O)
    (hb : ell ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ M) :
    ell ^ j * ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ ‖L‖ * M := by
  have h := L.norm_iteratedFDeriv_comp_left (hf.contDiffAt (hO.mem_nhds hx)) (n := j) (by simp)
  calc
    _ ≤ ell ^ j * (‖L‖ * ‖iteratedFDeriv ℝ j f x‖) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hell j)
    _ = ‖L‖ * (ell ^ j * ‖iteratedFDeriv ℝ j f x‖) := by ring
    _ ≤ ‖L‖ * M := mul_le_mul_of_nonneg_left hb L.opNorm_nonneg

theorem slow_bilinear_jet_bound_norm (L : X →L[ℝ] Y →L[ℝ] Z)
    (O : Set D) (hO : IsOpen O) (f : D → X) (g : D → Y)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (j : ℕ) (ell M K : ℝ) (hell : 0 ≤ ell) (x : D) (hx : x ∈ O)
    (hfb : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ M)
    (hgb : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k g x‖ ≤ K) :
    ell ^ j * ‖iteratedFDeriv ℝ j (fun y => L (f y) (g y)) x‖ ≤
      2 ^ j * (‖L‖ * M) * K := by
  have hLf : ContDiffOn ℝ ∞ (L ∘ f) O := L.contDiff.comp_contDiffOn hf
  have hb (k : ℕ) (hk : k ≤ j) :
      ell ^ k * ‖iteratedFDeriv ℝ k (L ∘ f) x‖ ≤ ‖L‖ * M :=
    slow_linear_jet_bound L O hO f hf k ell M hell x hx (hfb k hk)
  simpa only [Nat.add_zero, comp_apply] using
    scaled_clm_apply O hO (L ∘ f) g hLf hg j 0 ell (‖L‖ * M) K hell hb
      (fun k hk => by simpa using hgb k hk) hx

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.slow_bilinear_jet_bound_norm
