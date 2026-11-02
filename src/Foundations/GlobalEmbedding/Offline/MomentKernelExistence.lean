import GlobalEmbedding.Offline.MomentKernel
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual finite-moment smoothing template in every coordinate dimension

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`thm:repair`, lines 700–702; dependency `repair-moment-kernel`.

Choose a native normalized smooth bump with outer radius `rho / 2`, then
apply the explicit finite signed dilation construction. Its topological
support is contained in the prescribed open `rho`-ball, its integral is
one, and all coordinate moments of positive total degree at most `r`
vanish. Every fixed derivative has finite L1 norm, and every absolute
coordinate moment is integrable. The theorem includes `d = 0` and `r = 0`
without changing the measure or introducing separate axioms.

This closes the isolated finite-moment kernel construction, not the
localized smoothing estimates or the full repair theorem.
-/

open MeasureTheory
open scoped BigOperators ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

/-- A coordinate monomial on the actual Euclidean coordinate space. -/
def coordinateMonomial {d : ℕ} (alpha : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, x i ^ alpha i

/-- Coordinate monomials are continuous, including the empty product in
dimension zero. -/
theorem coordinateMonomial_continuous {d : ℕ} (alpha : Fin d → ℕ) :
    Continuous (coordinateMonomial alpha) := by
  exact continuous_finsetProd Finset.univ fun i _ =>
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).pow _

/-- A coordinate monomial scales with its actual total degree. -/
theorem coordinateMonomial_smul {d : ℕ} (alpha : Fin d → ℕ)
    (a : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    coordinateMonomial alpha (a • x) =
      a ^ (∑ i, alpha i) * coordinateMonomial alpha x := by
  change (∏ i, (a * x i) ^ alpha i) = a ^ (∑ i, alpha i) * ∏ i, x i ^ alpha i
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Every coordinate dimension and every finite moment order admit an
actual smooth signed kernel inside any prescribed positive radius.

Proof: normalize the native bump with radii `rho / 4 < rho / 2` for
Lebesgue volume. The finite Lagrange-weighted dilations have integral one
and vanish against every positive-degree homogeneous monomial through
order `r`. They vanish outside the half-radius closed ball, so their
topological support lies inside the prescribed open ball. Smoothness and
compact support make all fixed derivatives and polynomial absolute
moments integrable. All constants are properties of this fixed template;
there is no subsequent smoothing scale or chart count among the inputs.
-/
theorem exists_smooth_finite_moment_kernel (d r : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    ∃ K : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ K ∧
      HasCompactSupport K ∧
      tsupport K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) rho ∧
      (∫ x, K x) = 1 ∧
      (∀ alpha : Fin d → ℕ, 0 < ∑ i, alpha i → (∑ i, alpha i) ≤ r →
        (∫ x, coordinateMonomial alpha x * K x) = 0) ∧
      (∀ j : ℕ, Integrable (fun x => ‖iteratedFDeriv ℝ j K x‖)) ∧
      (∀ alpha : Fin d → ℕ, Integrable (fun x => |coordinateMonomial alpha x * K x|)) := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    { rIn := rho / 4
      rOut := rho / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let kappa : EuclideanSpace ℝ (Fin d) → ℝ := b.normed volume
  have hsmooth : ContDiff ℝ ∞ kappa := b.contDiff_normed
  have hcompact : HasCompactSupport kappa := b.hasCompactSupport_normed
  have hmass : (∫ x, kappa x) = 1 := b.integral_normed
  let K := finiteMomentKernel r kappa
  have hKsmooth : ContDiff ℝ ∞ K := finiteMomentKernel_contDiff hsmooth r
  have hKcompact : HasCompactSupport K := finiteMomentKernel_hasCompactSupport hcompact r
  have hzero : ∀ x : EuclideanSpace ℝ (Fin d), rho / 2 ≤ ‖x‖ → kappa x = 0 := by
    intro x hx
    have hn : x ∉ Function.support (b.normed volume) := by
      rw [b.support_normed_eq]
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
    by_contra hne
    exact hn hne
  refine ⟨K, hKsmooth, hKcompact, ?_, ?_, ?_, ?_, ?_⟩
  · have hs := finiteMomentKernel_tsupport_subset hzero r
    exact hs.trans (Metric.closedBall_subset_ball (by linarith))
  · exact finiteMomentKernel_integral volume hsmooth hcompact hmass r
  · intro alpha hpos hle
    exact finiteMomentKernel_homogeneous_moment volume hsmooth hcompact r
      (coordinateMonomial alpha) (coordinateMonomial_continuous alpha) hpos hle
      (coordinateMonomial_smul alpha)
  · intro j
    exact finiteMomentKernel_integrable_derivative volume hsmooth hcompact r j
  · intro alpha
    have hint : Integrable (fun x => coordinateMonomial alpha x * K x) :=
      ((coordinateMonomial_continuous alpha).mul hKsmooth.continuous).integrable_of_hasCompactSupport
        hKcompact.mul_left
    simpa only [Real.norm_eq_abs] using hint.norm

end

end GlobalEmbedding.Offline
