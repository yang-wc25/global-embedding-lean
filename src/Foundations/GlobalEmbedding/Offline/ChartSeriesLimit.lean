import GlobalEmbedding.Offline.SmoothSeries
import GlobalEmbedding.Offline.MetricLimit
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The same coordinate series has the actual manifold differential limit

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `thm:repair`,
lines 772–778; DAG nodes `repair-finite-wait-convergence` and
`repair-mathlib-uniform-derivative-limit`.

The increments are actual maps on the original manifold. On each fixed extended
chart, their actual coordinate derivatives satisfy the eventual summable bounds
from `SmoothSeries`. This file transfers the resulting smoothness and first
derivative convergence to the same pointwise sum on the manifold. The derivatives
are native `mvfderiv`, and the last result uses the original `inducedMetric`.

Differentiability is established before using the native chart formula for
`mvfderiv`; no undefined derivative branch is silently identified with a chart
derivative. Different points and derivative orders may have different constants,
buffers and waiting times. This supplies the limit passage, while obtaining the
geometric increment estimates and retained phase margins remains a separate task.
-/

open Filter Set Manifold
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual smoothness on an open coordinate buffer gives smoothness of the same
map at the chart centre. The native source-chart characterization also supplies
the continuity required in the definition of manifold smoothness. -/
theorem contMDiffAt_of_contDiffOn_extChartAt
    {f : M → F} {x : M} {U : Set E} {r : ℕ∞ω}
    (hU : IsOpen U) (hx : extChartAt I x x ∈ U)
    (hf : ContDiffOn ℝ r (f ∘ (extChartAt I x).symm) U) :
    ContMDiffAt I 𝓘(ℝ, F) r f x := by
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  exact ((hf _ hx).contDiffAt (hU.mem_nhds hx)).contDiffWithinAt

/-- Convergence of the actual first iterated derivatives gives convergence of
the actual continuous linear derivatives on a domain of unique differentiability.
The equality of the two native operator-norm distances is used directly. -/
theorem tendstoUniformlyOn_fderivWithin_of_iterated_one
    {fseq : ℕ → E → F} {f : E → F} {U : Set E}
    (hU : UniqueDiffOn ℝ U)
    (h : TendstoUniformlyOn (fun n ↦ iteratedFDerivWithin ℝ 1 (fseq n) U)
      (iteratedFDerivWithin ℝ 1 f U) atTop U) :
    TendstoUniformlyOn (fun n ↦ fderivWithin ℝ (fseq n) U)
      (fderivWithin ℝ f U) atTop U := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn
  intro x hx
  simpa only [dist_iteratedFDerivWithin_one _ _ (hU x hx) (hU x hx)] using hn x hx

/-- A smooth coordinate representative on an open buffer computes the native
ambient derivative. Unique differentiability of `range I` identifies its
within-derivative with the genuine derivative of this smooth representative.
This remains valid for models with boundary whenever the stated buffer exists. -/
theorem mvfderiv_eq_fderivWithin_extChartAt
    {f : M → F} {x : M} {U : Set E}
    (hU : IsOpen U) (hx : extChartAt I x x ∈ U)
    (hf : ContDiffOn ℝ ∞ (f ∘ (extChartAt I x).symm) U) :
    mvfderiv I f x =
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) U (extChartAt I x x)) ∘L
        (tangentSpaceCastModel I x) := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, F) f x :=
    (contMDiffAt_of_contDiffOn_extChartAt hU hx hf).mdifferentiableAt (by simp)
  have hd : DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    ((hf _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  ext v
  simp only [mvfderiv, hmd.mfderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp]
  rw [fderivWithin_eq_fderiv (I.uniqueDiffOn _ (extChartAt_target_subset_range _
    (mem_extChartAt_target x))) hd, fderivWithin_of_mem_nhds (hU.mem_nhds hx)]

variable [CompleteSpace F]

/-- Tail-only bounds for the actual coordinate increments produce a genuine
summable series, a smooth limit at the chart centre, and operator-norm convergence
of the actual ambient derivatives of the finite partial sums.

Source: `thm:repair`, lines 772–778. The zeroth bound proves summability at the
actual manifold point. `SmoothSeries` proves smoothness of the same pointwise sum
and uniform convergence of its first iterated coordinate derivative. The native
distance identity converts this to continuous-linear-map convergence. All maps
are shown differentiable before their manifold derivative is computed, and the
fixed source tangent identification is applied continuously. -/
theorem smooth_tsum_at_and_tendsto_mvfderiv_of_eventual_chart_bound
    (f : ℕ → M → F) (t : ℕ → ℝ) {x : M} {U : Set E}
    (hU : IsOpen U) (hx : extChartAt I x x ∈ U)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n ∘ (extChartAt I x).symm) U)
    (ht : Summable t)
    (hbound : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ U,
      ‖iteratedFDerivWithin ℝ k (f n ∘ (extChartAt I x).symm) U y‖ ≤ C * t n) :
    Summable (fun n ↦ f n x) ∧
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y ↦ ∑' n, f n y) x ∧
    Tendsto (fun N ↦ mvfderiv I (fun y ↦ ∑ n ∈ Finset.range N, f n y) x) atTop
      (𝓝 (mvfderiv I (fun y ↦ ∑' n, f n y) x)) := by
  have hs := smooth_series_on_of_eventual_scaled_bound hU
    (fun n ↦ f n ∘ (extChartAt I x).symm) t hf ht hbound
  have hsumSmooth : ContDiffOn ℝ ∞
      ((fun y ↦ ∑' n, f n y) ∘ (extChartAt I x).symm) U := by
    simpa only [Function.comp_def] using hs.1
  have hpartialSmooth (N : ℕ) : ContDiffOn ℝ ∞
      ((fun y ↦ ∑ n ∈ Finset.range N, f n y) ∘ (extChartAt I x).symm) U := by
    simpa only [Function.comp_def] using
      ContDiffOn.sum (fun n (_hn : n ∈ Finset.range N) ↦ hf n)
  refine ⟨?_, contMDiffAt_of_contDiffOn_extChartAt hU hx hsumSmooth, ?_⟩
  · obtain ⟨C, N, hN⟩ := hbound 0
    apply Summable.of_norm_bounded_eventually_nat (ht.mul_left C)
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [norm_iteratedFDerivWithin_zero, Function.comp_apply, extChartAt_to_inv]
      using hN n hn _ hx
  · have hcoord :=
      (tendstoUniformlyOn_fderivWithin_of_iterated_one hU.uniqueDiffOn (hs.2.2 1)).tendsto_at hx
    let : IsNormableSpace ℝ (TangentSpace I x) :=
      (tangentSpaceCastModel I x).isNormableSpace
    have hcomp : Continuous (fun L : E →L[ℝ] F ↦
        L.comp (tangentSpaceCastModel I x).toContinuousLinearMap) :=
      continuous_id.clm_comp_const _
    have hlimit := (hcomp.tendsto
      (fderivWithin ℝ (fun y ↦ ∑' n, f n ((extChartAt I x).symm y)) U
        (extChartAt I x x))).comp hcoord
    simpa only [mvfderiv_eq_fderivWithin_extChartAt hU hx hsumSmooth,
      mvfderiv_eq_fderivWithin_extChartAt hU hx (hpartialSmooth _), Function.comp_def]
      using hlimit

/-- Pointwise coordinate buffers give one globally smooth sum and convergence of
its actual manifold differentials at every point.

Source: `thm:repair`, lines 776–778. Each buffer and each derivative order may have
its own finite waiting time. No global uniform estimate, finite atlas cardinality,
or common waiting time for all orders is inserted in the conclusion. -/
theorem smooth_tsum_and_tendsto_mvfderiv_of_eventual_chart_bound
    (f : ℕ → M → F) (t : ℕ → ℝ) (ht : Summable t)
    (hchart : ∀ x : M, ∃ U : Set E,
      IsOpen U ∧ extChartAt I x x ∈ U ∧
      (∀ n, ContDiffOn ℝ ∞ (f n ∘ (extChartAt I x).symm) U) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ U,
        ‖iteratedFDerivWithin ℝ k (f n ∘ (extChartAt I x).symm) U y‖ ≤ C * t n)) :
    (∀ x, Summable (fun n ↦ f n x)) ∧
    ContMDiff I 𝓘(ℝ, F) ∞ (fun y ↦ ∑' n, f n y) ∧
    (∀ x, Tendsto (fun N ↦ mvfderiv I (fun y ↦ ∑ n ∈ Finset.range N, f n y) x) atTop
      (𝓝 (mvfderiv I (fun y ↦ ∑' n, f n y) x))) := by
  have h (x : M) : Summable (fun n ↦ f n x) ∧
      ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y ↦ ∑' n, f n y) x ∧
      Tendsto (fun N ↦ mvfderiv I (fun y ↦ ∑ n ∈ Finset.range N, f n y) x) atTop
        (𝓝 (mvfderiv I (fun y ↦ ∑' n, f n y) x)) := by
    obtain ⟨U, hU, hx, hf, hbound⟩ := hchart x
    exact smooth_tsum_at_and_tendsto_mvfderiv_of_eventual_chart_bound f t hU hx hf ht hbound
  exact ⟨fun x ↦ (h x).1, fun x ↦ (h x).2.1, fun x ↦ (h x).2.2⟩

/-- The actual iterates may start from any smooth base map, with no quantitative
bound on that finite initial term.

Source: `thm:repair`, line 776. The iterates are exactly `F0 + sum (range N) f`,
and the limit is exactly `F0 + tsum f`. This formulation aligns the analytic
series result with the actual repair iterates without an artificial zero stage. -/
theorem smooth_base_add_tsum_and_tendsto_mvfderiv
    (F0 : M → F) (f : ℕ → M → F) (t : ℕ → ℝ)
    (hF0 : ContMDiff I 𝓘(ℝ, F) ∞ F0) (ht : Summable t)
    (hchart : ∀ x : M, ∃ U : Set E,
      IsOpen U ∧ extChartAt I x x ∈ U ∧
      (∀ n, ContDiffOn ℝ ∞ (f n ∘ (extChartAt I x).symm) U) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ U,
        ‖iteratedFDerivWithin ℝ k (f n ∘ (extChartAt I x).symm) U y‖ ≤ C * t n)) :
    (∀ x, Summable (fun n ↦ f n x)) ∧
    ContMDiff I 𝓘(ℝ, F) ∞ (fun y ↦ F0 y + ∑' n, f n y) ∧
    (∀ x, Tendsto
      (fun N ↦ mvfderiv I (fun y ↦ F0 y + ∑ n ∈ Finset.range N, f n y) x) atTop
      (𝓝 (mvfderiv I (fun y ↦ F0 y + ∑' n, f n y) x))) := by
  have hs := smooth_tsum_and_tendsto_mvfderiv_of_eventual_chart_bound f t ht hchart
  have hterm (n : ℕ) : ContMDiff I 𝓘(ℝ, F) ∞ (f n) := by
    intro x
    obtain ⟨U, hU, hx, hf, _hbound⟩ := hchart x
    exact contMDiffAt_of_contDiffOn_extChartAt hU hx (hf n)
  have hpartial (N : ℕ) :
      ContMDiff I 𝓘(ℝ, F) ∞ (fun y ↦ ∑ n ∈ Finset.range N, f n y) :=
    ContMDiff.sum fun n _hn ↦ hterm n
  refine ⟨hs.1, hF0.add hs.2.1, ?_⟩
  intro x
  have hbaseDiff := hF0.mdifferentiableAt (x := x) (by simp)
  have hsumDiff := hs.2.1.mdifferentiableAt (x := x) (by simp)
  have hpartialDiff (N : ℕ) := (hpartial N).mdifferentiableAt (x := x) (by simp)
  simpa only [mvfderiv_fun_add hbaseDiff hsumDiff,
    mvfderiv_fun_add hbaseDiff (hpartialDiff _)] using
    (tendsto_const_nhds.add (hs.2.2 x) :
      Tendsto (fun N ↦ mvfderiv I F0 x +
        mvfderiv I (fun y ↦ ∑ n ∈ Finset.range N, f n y) x) atTop
        (𝓝 (mvfderiv I F0 x + mvfderiv I (fun y ↦ ∑' n, f n y) x)))

/-- The actual repair series has the prescribed original induced metric once
its normalized defects have the stated vanishing scale and eventual bounds.

Source: `thm:repair`, line 776. This joins the proved coordinate-series limit to
the original metric limit. It neither assumes differential convergence nor
replaces the geometric metric by abstract data: both the approximating metrics
and the final metric are `GlobalEmbedding.Paper.inducedMetric` of the displayed
actual maps. The still separate geometric obligations are precisely the smooth
coordinate increment estimates and the normalized-defect identity and bounds. -/
theorem smooth_repair_series_metric_limit
    {N : ℕ} (F0 : M → EuclideanSpace ℝ (Fin N))
    (f : ℕ → M → EuclideanSpace ℝ (Fin N)) (t delta : ℕ → ℝ)
    (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (Hseq : ℕ → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (hF0 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F0)
    (ht : Summable t)
    (hchart : ∀ x : M, ∃ U : Set E,
      IsOpen U ∧ extChartAt I x x ∈ U ∧
      (∀ n, ContDiffOn ℝ ∞ (f n ∘ (extChartAt I x).symm) U) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∃ K : ℕ, ∀ n ≥ K, ∀ y ∈ U,
        ‖iteratedFDerivWithin ℝ k (f n ∘ (extChartAt I x).symm) U y‖ ≤ C * t n))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      ∃ C : ℝ, ∀ᶠ n in atTop, ‖Hseq n x v w‖ ≤ C)
    (hdefect : ∀ n x, g x - GlobalEmbedding.Paper.inducedMetric (I := I)
      (fun y ↦ F0 y + ∑ j ∈ Finset.range n, f j y) x = delta n ^ 2 • Hseq n x) :
    (∀ x, Summable (fun n ↦ f n x)) ∧
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (fun y ↦ F0 y + ∑' n, f n y) ∧
    GlobalEmbedding.Paper.inducedMetric (I := I) (fun y ↦ F0 y + ∑' n, f n y) = g := by
  have hs := smooth_base_add_tsum_and_tendsto_mvfderiv F0 f t hF0 ht hchart
  refine ⟨hs.1, hs.2.1, ?_⟩
  exact inducedMetric_eq_of_tendsto_mvfderiv
    (fun n y ↦ F0 y + ∑ j ∈ Finset.range n, f j y)
    (fun y ↦ F0 y + ∑' n, f n y) g Hseq delta hs.2.2 hdelta hH hdefect

#print axioms contMDiffAt_of_contDiffOn_extChartAt
#print axioms tendstoUniformlyOn_fderivWithin_of_iterated_one
#print axioms mvfderiv_eq_fderivWithin_extChartAt
#print axioms smooth_tsum_at_and_tendsto_mvfderiv_of_eventual_chart_bound
#print axioms smooth_tsum_and_tendsto_mvfderiv_of_eventual_chart_bound
#print axioms smooth_base_add_tsum_and_tendsto_mvfderiv
#print axioms smooth_repair_series_metric_limit

end GlobalEmbedding.Offline
