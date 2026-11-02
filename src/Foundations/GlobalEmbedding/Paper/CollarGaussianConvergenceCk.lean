import GlobalEmbedding.Paper.CollarGaussianDerivativeConvolution
import GlobalEmbedding.Paper.CollarGaussianUniformApproximateIdentity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Source Gaussian approximants converge in every actual global Ck supremum norm

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof line 520. The order is genuine C∞, and the limit takes the supremum of actual iterated
Frechet derivative operator norms over the entire real domain and all orders up to k.
-/

open MeasureTheory Filter Metric Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The actual normalized Gaussian convolution of a smooth compactly supported map is smooth,
every actual derivative converges globally uniformly, and its genuine global Ck supremum
error tends to zero for every finite k.

Source: Proposition `prop:collar`, proof line 520; the full finite-smooth-norm assertion.
Each actual iterated derivative of f is continuous with compact support. Its actual norm is
bounded and its limit at infinity is zero, hence it is uniformly continuous. Apply the proved
global Gaussian approximate identity in that actual multilinear operator space, and use the
proved all-order derivative convolution identity. For a fixed k and positive eta, intersect
these finitely many uniform estimates at tolerance eta/2. The actual error norms are then all
bounded above by eta/2, so both actual real suprema exist and their supremum is nonnegative
and at most eta/2. This proves convergence of the actual global Ck supremum error to zero.
No analytic input, pointwise-only substitute, restricted compact domain, or derivative cutoff
in the smoothness assumption is used. The codomain may be any real Banach space, and zero
orders and domain/codomain dimensions are included. -/
theorem collar_gaussian_convergence_Ck
    {d : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : EuclideanSpace ℝ (Fin d) → W) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport f) :
    let G : ℝ → EuclideanSpace ℝ (Fin d) → W := fun ε x ↦
      ∫ y : EuclideanSpace ℝ (Fin d),
        ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • f y
    (∀ ε : ℝ, 0 < ε → ContDiff ℝ ∞ (G ε)) ∧
    (∀ n : ℕ, TendstoUniformly (fun ε ↦ iteratedFDeriv ℝ n (G ε))
      (iteratedFDeriv ℝ n f) (𝓝[>] 0)) ∧
    ∀ k : ℕ, Tendsto
      (fun ε : ℝ ↦ ⨆ n : Fin (k + 1), ⨆ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ n.val (G ε) x - iteratedFDeriv ℝ n.val f x‖)
      (𝓝[>] 0) (𝓝 0) := by
  let V := EuclideanSpace ℝ (Fin d)
  let G : ℝ → V → W := fun ε x ↦ ∫ y : V,
    ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • f y
  change (∀ ε : ℝ, 0 < ε → ContDiff ℝ ∞ (G ε)) ∧
    (∀ n : ℕ, TendstoUniformly (fun ε ↦ iteratedFDeriv ℝ n (G ε))
      (iteratedFDeriv ℝ n f) (𝓝[>] 0)) ∧ _
  have hreg (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (G ε) :=
    (collar_gaussian_derivative_convolution ε hε f hf hcompact).1
  have hu (n : ℕ) : TendstoUniformly (fun ε ↦ iteratedFDeriv ℝ n (G ε))
      (iteratedFDeriv ℝ n f) (𝓝[>] 0) := by
    have hc : Continuous (iteratedFDeriv ℝ n f) :=
      hf.continuous_iteratedFDeriv (by simp)
    have huc : UniformContinuous (iteratedFDeriv ℝ n f) :=
      hc.uniformContinuous_of_tendsto_cocompact (hcompact.iteratedFDeriv n).is_zero_at_infty
    obtain ⟨C, _, hC⟩ := hcompact.exists_bound_iteratedFDeriv hf n
    have happrox := collar_gaussian_uniform_approximate_identity
      (iteratedFDeriv ℝ n f) huc C (hC n le_rfl)
    apply Metric.tendstoUniformly_iff.mpr
    intro η hη
    filter_upwards [self_mem_nhdsWithin,
      Metric.tendstoUniformly_iff.mp happrox η hη] with ε (hε : 0 < ε) hclose
    intro x
    have hd := (collar_gaussian_derivative_convolution ε hε f hf hcompact).2 n x
    change iteratedFDeriv ℝ n (G ε) x = _ at hd
    rw [hd]
    exact hclose x
  refine ⟨hreg, hu, ?_⟩
  intro k
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ n : Fin (k + 1), ∀ x : V,
      ‖iteratedFDeriv ℝ n.val (G ε) x - iteratedFDeriv ℝ n.val f x‖ < η / 2 := by
    apply Filter.eventually_all.mpr
    intro n
    filter_upwards [Metric.tendstoUniformly_iff.mp (hu n.val) (η / 2) (by positivity)]
      with ε hclose
    intro x
    simpa only [dist_eq_norm, norm_sub_rev] using hclose x
  filter_upwards [hs] with ε hsmall
  let e : Fin (k + 1) → V → ℝ := fun n x ↦
    ‖iteratedFDeriv ℝ n.val (G ε) x - iteratedFDeriv ℝ n.val f x‖
  have hb (n : Fin (k + 1)) : BddAbove (range (e n)) := by
    refine ⟨η / 2, ?_⟩
    rintro b ⟨x, rfl⟩
    exact (hsmall n x).le
  have hinner (n : Fin (k + 1)) : (⨆ x : V, e n x) ≤ η / 2 :=
    ciSup_le (fun x ↦ (hsmall n x).le)
  have houter : BddAbove (range (fun n : Fin (k + 1) ↦ ⨆ x : V, e n x)) := by
    refine ⟨η / 2, ?_⟩
    rintro b ⟨n, rfl⟩
    exact hinner n
  have hnonneg : 0 ≤ ⨆ n : Fin (k + 1), ⨆ x : V, e n x :=
    le_ciSup_of_le houter 0 (le_ciSup_of_le (hb 0) 0 (norm_nonneg _))
  change dist (⨆ n : Fin (k + 1), ⨆ x : V, e n x) 0 < η
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (ciSup_le hinner).trans_lt (by linarith)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_gaussian_convergence_Ck
