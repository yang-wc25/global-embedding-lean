import GlobalEmbedding.Offline.MomentKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A fixed actual smoothing template on any finite-dimensional coordinate model

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–702,
`repair-moment-kernel`. Mathlib's finite-dimensional bump instance makes
the construction available on the original Pi-sup coordinate model and
on genuine parameter/source products, as well as on Euclidean space.
The measure is the actual supplied Haar measure, including Lebesgue
volume. No choice of smoothing scale or atlas appears in the template.
-/

open MeasureTheory
open scoped ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [mu.IsAddHaarMeasure]

/-- The normalized native bump with fixed inner and outer radii.
Finite-dimensional bump existence is supplied by pinned Mathlib. -/
def normalizedSmoothingBase (rho : ℝ) (hrho : 0 < rho) : E → ℝ :=
  let b : ContDiffBump (0 : E) :=
    { rIn := rho / 4
      rOut := rho / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  b.normed mu

/-- All base-template requirements follow from the native normalized
bump, including true unit mass for the actual Haar measure. -/
theorem normalizedSmoothingBase_spec (rho : ℝ) (hrho : 0 < rho) :
    ContDiff ℝ ∞ (normalizedSmoothingBase mu rho hrho) ∧
      HasCompactSupport (normalizedSmoothingBase mu rho hrho) ∧
      (∫ x, normalizedSmoothingBase mu rho hrho x ∂mu) = 1 ∧
      (∀ x : E, rho / 2 ≤ ‖x‖ → normalizedSmoothingBase mu rho hrho x = 0) := by
  let b : ContDiffBump (0 : E) :=
    { rIn := rho / 4
      rOut := rho / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  change ContDiff ℝ ∞ (b.normed mu) ∧ HasCompactSupport (b.normed mu) ∧
    (∫ x, b.normed mu x ∂mu) = 1 ∧ _
  refine ⟨b.contDiff_normed, b.hasCompactSupport_normed, b.integral_normed, ?_⟩
  intro x hx
  have hn : x ∉ Function.support (b.normed mu) := by
    rw [b.support_normed_eq]
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  exact Function.notMem_support.mp hn

/-- The actual signed order-r template, fixed before any convolution
scale or chart family is introduced. -/
def fixedSmoothingKernel (rho : ℝ) (hrho : 0 < rho) (r : ℕ) : E → ℝ :=
  finiteMomentKernel r (normalizedSmoothingBase mu rho hrho)

/-- The fixed template has compact support strictly inside the requested
radius, true unit mass, all homogeneous moments through r zero, finite
L1 norms of all actual derivatives, and finite absolute radial moments.
It applies directly to Pi coordinates and parameter products, including
the zero-dimensional model. -/
theorem fixedSmoothingKernel_spec (rho : ℝ) (hrho : 0 < rho) (r : ℕ) :
    let K := fixedSmoothingKernel mu rho hrho r
    ContDiff ℝ ∞ K ∧ HasCompactSupport K ∧ tsupport K ⊆ Metric.ball (0 : E) rho ∧
      (∫ x, K x ∂mu) = 1 ∧
      (∀ k : ℕ, 0 < k → k ≤ r → ∀ P : E → ℝ, Continuous P →
        (∀ (a : ℝ) (x : E), P (a • x) = a ^ k * P x) → (∫ x, P x * K x ∂mu) = 0) ∧
      (∀ j : ℕ, Integrable (fun x => ‖iteratedFDeriv ℝ j K x‖) mu) ∧
      (∀ s : ℕ, Integrable (fun x => |K x| * ‖x‖ ^ s) mu) := by
  let kappa := normalizedSmoothingBase mu rho hrho
  have hb := normalizedSmoothingBase_spec mu rho hrho
  have hsmooth : ContDiff ℝ ∞ kappa := hb.1
  have hcompact : HasCompactSupport kappa := hb.2.1
  have hmass : (∫ x, kappa x ∂mu) = 1 := hb.2.2.1
  let K := fixedSmoothingKernel mu rho hrho r
  have hKs : ContDiff ℝ ∞ K := finiteMomentKernel_contDiff hsmooth r
  have hKc : HasCompactSupport K := finiteMomentKernel_hasCompactSupport hcompact r
  refine ⟨hKs, hKc, ?_, finiteMomentKernel_integral mu hsmooth hcompact hmass r, ?_, ?_, ?_⟩
  · exact (finiteMomentKernel_tsupport_subset hb.2.2.2 r).trans
      (Metric.closedBall_subset_ball (by linarith))
  · intro k hk hkr P hP hhom
    exact finiteMomentKernel_homogeneous_moment mu hsmooth hcompact r P hP hk hkr hhom
  · intro j
    exact finiteMomentKernel_integrable_derivative mu hsmooth hcompact r j
  · intro s
    exact (hKs.continuous.abs.mul (continuous_norm.pow s)).integrable_of_hasCompactSupport
      hKc.abs.mul_right

end

end GlobalEmbedding.Offline
