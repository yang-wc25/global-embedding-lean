import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# One smooth sum on a buffered coordinate domain

Source: `literature/parallelizable-stable-plus-one/main.tex`, the proof of `thm:repair`,
lines 772–778; DAG nodes `repair-finite-wait-convergence` and
`repair-mathlib-uniform-derivative-limit`.

The coordinate domain is the actual open set `U`. All derivative norms are the native
operator norms of `iteratedFDerivWithin`, and the limit is the same pointwise `tsum` at
every order. For each order separately, only a tail of the sequence has to satisfy a
summable uniform bound. The finite initial part only needs to be smooth on `U`.

Mathlib already has `contDiff_tsum_of_eventually` on the whole source space. Its
`hasFDerivAt_of_tendstoUniformlyOn` and `tendstoUniformlyOn_tsum_nat_eventually`
provide the ingredients for the open-domain version needed by buffered charts.
The source may itself be a product of source and parameter coordinates.
-/

open Filter Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Differentiate the same pointwise series on an open coordinate domain, using an
order-dependent tail bound for its actual derivatives.

Source: `thm:repair`, lines 772–778; derivative-limit DAG leaf. Uniform convergence
of the derivative series follows from Mathlib's eventual Weierstrass test. Its
uniform derivative-limit theorem applies to the actual finite partial sums, whose
values converge to the given pointwise `tsum`. No estimate on the finitely many
initial derivative functions is imposed. -/
theorem hasFDerivAt_tsum_on_of_eventually
    {U : Set E} (hU : IsOpen U)
    {f : ℕ → E → F} {f' : ℕ → E → E →L[ℝ] F} {v : ℕ → ℝ}
    (hv : Summable v)
    (hf : ∀ n x, x ∈ U → HasFDerivAt (f n) (f' n x) x)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ U, ‖f' n x‖ ≤ v n)
    (hsum : ∀ x ∈ U, Summable (fun n ↦ f n x))
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∑' n, f n y) (∑' n, f' n x) x := by
  refine hasFDerivAt_of_tendstoUniformlyOn
    (f := fun N y ↦ ∑ n ∈ Finset.range N, f n y) hU
    (tendstoUniformlyOn_tsum_nat_eventually hv hbound) ?_ ?_ hx
  · intro N y hy
    exact HasFDerivAt.fun_sum fun n _hn ↦ hf n y hy
  · intro y hy
    exact (hsum y hy).hasSum.tendsto_sum_nat

/-- The actual series of each fixed derivative converges at every point of the domain.

Source: `thm:repair`, lines 772–778. Apply the eventual comparison test in the
native Banach space of continuous multilinear maps. This explicitly verifies
summability, independently of the total definition of `tsum`. -/
theorem summable_iteratedFDerivWithin_on_of_eventually
    {U : Set E} (f : ℕ → E → F) (v : ℕ → ℝ) (k : ℕ)
    (hv : Summable v)
    (hbound : ∀ᶠ n in atTop,
      ∀ x ∈ U, ‖iteratedFDerivWithin ℝ k (f n) U x‖ ≤ v n)
    {x : E} (hx : x ∈ U) :
    Summable (fun n ↦ iteratedFDerivWithin ℝ k (f n) U x) := by
  apply Summable.of_norm_bounded_eventually_nat hv
  filter_upwards [hbound] with n hn
  exact hn x hx

/-- Open-domain smooth-series theorem with independent finite waiting times at every order.

Source: `thm:repair`, lines 772–778; DAG `repair-finite-wait-convergence`.
The eventual comparison test gives pointwise summability of each derivative series.
Apply the preceding first-derivative result successively to those actual series.
The recursive definition of `iteratedFDerivWithin`, and its native currying linear
isometry, identify every derivative with a derivative of the SAME pointwise sum.
Thus all orders are smooth and the actual derivatives of the finite partial sums
converge uniformly to the corresponding derivatives of that one sum.

The domain may be empty, disconnected, or unbounded. No compactness, common tail for
all orders, or bound on the finite initial part is assumed. -/
theorem smooth_series_on_of_eventually
    {U : Set E} (hU : IsOpen U)
    (f : ℕ → E → F) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hv : ∀ k, Summable (v k))
    (hbound : ∀ k, ∀ᶠ n in atTop,
      ∀ x ∈ U, ‖iteratedFDerivWithin ℝ k (f n) U x‖ ≤ v k n) :
    ContDiffOn ℝ ∞ (fun x ↦ ∑' n, f n x) U ∧
    (∀ k x, x ∈ U →
      iteratedFDerivWithin ℝ k (fun y ↦ ∑' n, f n y) U x =
        ∑' n, iteratedFDerivWithin ℝ k (f n) U x) ∧
    (∀ k, TendstoUniformlyOn
      (fun N ↦ iteratedFDerivWithin ℝ k (fun x ↦ ∑ n ∈ Finset.range N, f n x) U)
      (iteratedFDerivWithin ℝ k (fun x ↦ ∑' n, f n x) U) atTop U) := by
  let g (k : ℕ) (x : E) := ∑' n, iteratedFDerivWithin ℝ k (f n) U x
  have hsum (k : ℕ) (x : E) (hx : x ∈ U) :
      Summable (fun n ↦ iteratedFDerivWithin ℝ k (f n) U x) :=
    summable_iteratedFDerivWithin_on_of_eventually f (v k) k (hv k) (hbound k) hx
  have hderiv (k : ℕ) (x : E) (hx : x ∈ U) :
      HasFDerivAt (g k)
        (∑' n, fderivWithin ℝ (iteratedFDerivWithin ℝ k (f n) U) U x) x := by
    apply hasFDerivAt_tsum_on_of_eventually
      (f := fun n ↦ iteratedFDerivWithin ℝ k (f n) U) hU (hv (k + 1))
    · intro n y hy
      exact ((hf n).differentiableOn_iteratedFDerivWithin (m := k)
        (by exact_mod_cast (ENat.natCast_lt_top k))
        hU.uniqueDiffOn y hy).hasFDerivWithinAt.hasFDerivAt (hU.mem_nhds hy)
    · filter_upwards [hbound (k + 1)] with n hn
      intro y hy
      simpa only [norm_fderivWithin_iteratedFDerivWithin] using hn y hy
    · exact hsum k
    · exact hx
  have hidentity : ∀ k,
      EqOn (iteratedFDerivWithin ℝ k (fun y ↦ ∑' n, f n y) U) (g k) U := by
    intro k
    induction k with
    | zero =>
        intro x _hx
        simp_rw [g, iteratedFDerivWithin_zero_eq_comp, Function.comp_apply]
        exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
    | succ k ih =>
        intro x hx
        rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
          fderivWithin_congr' ih hx,
          (hderiv k x hx).hasFDerivWithinAt.fderivWithin (hU.uniqueDiffOn x hx)]
        change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F).symm
            (∑' n, fderivWithin ℝ (iteratedFDerivWithin ℝ k (f n) U) U x) = _
        simpa only [g, iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F).symm.toContinuousLinearEquiv.map_tsum
  refine ⟨?_, fun k x hx ↦ hidentity k hx, ?_⟩
  · apply contDiffOn_of_differentiableOn
    intro k _hk
    have hd : DifferentiableOn ℝ (g k) U :=
      fun x hx ↦ (hderiv k x hx).differentiableAt.differentiableWithinAt
    exact hd.congr (hidentity k)
  · intro k
    have hu := tendstoUniformlyOn_tsum_nat_eventually (hv k) (hbound k)
    have hu' := hu.congr_right (fun x hx ↦ (hidentity k hx).symm)
    apply hu'.congr
    exact Eventually.of_forall fun N x hx ↦
      (iteratedFDerivWithin_fun_sum_apply hU.uniqueDiffOn hx
        (fun n _hn ↦ (hf n x hx).of_le (by simp))).symm

/-- A single summable scale sequence suffices, with a separate finite start and
constant for each derivative order.

Source: `thm:repair`, lines 772–778; after the stage tends to infinity the paper
bounds every fixed derivative of the increment by a constant times its summable
scale. Choose the constants order by order and apply the open-domain theorem.
There is no common finite waiting time imposed on all orders. -/
theorem smooth_series_on_of_eventual_scaled_bound
    {U : Set E} (hU : IsOpen U)
    (f : ℕ → E → F) (t : ℕ → ℝ)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (ht : Summable t)
    (hbound : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      ∀ x ∈ U, ‖iteratedFDerivWithin ℝ k (f n) U x‖ ≤ C * t n) :
    ContDiffOn ℝ ∞ (fun x ↦ ∑' n, f n x) U ∧
    (∀ k x, x ∈ U →
      iteratedFDerivWithin ℝ k (fun y ↦ ∑' n, f n y) U x =
        ∑' n, iteratedFDerivWithin ℝ k (f n) U x) ∧
    (∀ k, TendstoUniformlyOn
      (fun N ↦ iteratedFDerivWithin ℝ k (fun x ↦ ∑ n ∈ Finset.range N, f n x) U)
      (iteratedFDerivWithin ℝ k (fun x ↦ ∑' n, f n x) U) atTop U) := by
  choose C N hN using hbound
  apply smooth_series_on_of_eventually hU f (fun k n ↦ C k * t n) hf
  · intro k
    exact ht.mul_left (C k)
  · intro k
    exact eventually_atTop.2 ⟨N k, hN k⟩

#print axioms hasFDerivAt_tsum_on_of_eventually
#print axioms summable_iteratedFDerivWithin_on_of_eventually
#print axioms smooth_series_on_of_eventually
#print axioms smooth_series_on_of_eventual_scaled_bound

end GlobalEmbedding.Offline
