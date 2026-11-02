import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Freezing a genuine smooth coordinate coframe

Source: `prop:initialization`, main.tex 805--821.  These are local coordinate
producers: all constants are obtained from the given smooth field on a compact
coordinate domain, before K and T.  No derivative bound is an input.

The global selection of uniformly controlled charts and centers remains a
separate obligation; this file does not assert that the full proposition is closed.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Initialization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Compactness bounds the actual iterated derivatives of a field smooth on an
open neighborhood. The same sequence works for all points and is chosen before
any scale or center. Empty compact sets are allowed. -/
theorem exists_compact_smooth_derivative_bounds
    {s O : Set E} (hs : IsCompact s) (hO : IsOpen O) (hsO : s ⊆ O)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ j x, x ∈ s → ‖iteratedFDeriv ℝ j f x‖ ≤ B j := by
  have each (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    have hc : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) s :=
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hO (by simp)).norm).mono hsO
    obtain ⟨C, hC⟩ := hs.bddAbove_image hc
    refine ⟨max 0 C, le_max_left _ _, ?_⟩
    intro x hx
    exact (hC ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  choose B hB hbound using each
  exact ⟨B, hB, fun j x hx ↦ hbound j x hx⟩

/-- The actual affine phase determined by the value of a smooth coframe at a
center. Its derivative is precisely that frozen coframe, with no approximation.
This definition also works when the original chart is not a normal chart. -/
def frozenCoframePhase (θ : E → E →L[ℝ] F) (p : E) (x : E) : F := θ p (x - p)

theorem frozenCoframePhase_hasFDerivAt (θ : E → E →L[ℝ] F) (p x : E) :
    HasFDerivAt (frozenCoframePhase θ p) (θ p) x := by
  change HasFDerivAt (fun z : E ↦ θ p (z - p)) (θ p) x
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
    (θ p).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)

theorem frozenCoframePhase_fderiv (θ : E → E →L[ℝ] F) (p x : E) :
    fderiv ℝ (frozenCoframePhase θ p) x = θ p :=
  (frozenCoframePhase_hasFDerivAt θ p x).fderiv

/-- A smooth coframe on a fixed compact convex chart domain supplies its own
uniform freezing constant. In particular the O(K⁻¹) gain follows from actual
smoothness and the support radius, instead of being assumed. -/
theorem exists_frozenCoframe_error_bound
    {s O : Set E} (hs : IsCompact s) (hconv : Convex ℝ s)
    (hO : IsOpen O) (hsO : s ⊆ O)
    (θ : E → E →L[ℝ] F) (hθ : ContDiffOn ℝ ∞ θ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ K : ℝ), 0 ≤ ρ → 1 ≤ K →
      ∀ p ∈ s, ∀ x ∈ s, ‖x - p‖ ≤ ρ / K →
      ‖fderiv ℝ (frozenCoframePhase θ p) x - θ x‖ ≤ C * ρ / K := by
  obtain ⟨B, hB, hbound⟩ := exists_compact_smooth_derivative_bounds hs hO hsO θ hθ
  refine ⟨B 1, hB 1, ?_⟩
  intro ρ K hρ hK p hp x hx hxp
  rw [frozenCoframePhase_fderiv, norm_sub_rev]
  have hd (z : E) (hz : z ∈ s) : DifferentiableAt ℝ θ z :=
    (hθ.contDiffAt (hO.mem_nhds (hsO hz))).differentiableAt (by simp)
  have hb (z : E) (hz : z ∈ s) : ‖fderiv ℝ θ z‖ ≤ B 1 := by
    simpa only [norm_iteratedFDeriv_one] using hbound 1 z hz
  calc
    ‖θ x - θ p‖ ≤ B 1 * ‖x - p‖ :=
      hconv.norm_image_sub_le_of_norm_fderiv_le hd hb hp hx
    _ ≤ B 1 * (ρ / K) := mul_le_mul_of_nonneg_left hxp (hB 1)
    _ = B 1 * ρ / K := by ring

end GlobalEmbedding.Initialization
