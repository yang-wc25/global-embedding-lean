import GlobalEmbedding.Paper.CollarComplexRealGermUniqueness
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology

/-!
# Actual overlap compatibility for finite-coordinate complex analytic extensions

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Local extensions are constructed on balls with real centers.
-/

open Set Filter
open scoped Topology

namespace GlobalEmbedding.Paper

/-- Local complex analytic extensions of the same real function on complex balls with real
centers agree on their entire overlap.

Source: Proposition `prop:collar`, proof lines 530–534. Any point in the overlap has a real
part still in both balls, since coordinatewise real projection decreases the sup norm and
fixes both centers. On nearby real points both functions equal the same real data, so their
actual complex germs agree by real-germ uniqueness. The overlap is convex, hence connected;
the analytic identity principle propagates this equality over the entire overlap. The proof
also covers empty intersections and arbitrary radii without adding positivity assumptions. -/
theorem collar_complex_extension_overlap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    {m : ℕ} (G : (Fin m → ℝ) → F) (f h : (Fin m → ℂ) → F)
    (a b : Fin m → ℝ) (r s : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball (fun j ↦ (a j : ℂ)) r))
    (hh : AnalyticOnNhd ℂ h (Metric.ball (fun j ↦ (b j : ℂ)) s))
    (hfG : ∀ y : Fin m → ℝ, (fun j ↦ (y j : ℂ)) ∈
      Metric.ball (fun j ↦ (a j : ℂ)) r → f (fun j ↦ (y j : ℂ)) = G y)
    (hhG : ∀ y : Fin m → ℝ, (fun j ↦ (y j : ℂ)) ∈
      Metric.ball (fun j ↦ (b j : ℂ)) s → h (fun j ↦ (y j : ℂ)) = G y) :
    EqOn f h (Metric.ball (fun j ↦ (a j : ℂ)) r ∩
      Metric.ball (fun j ↦ (b j : ℂ)) s) := by
  intro z hz
  let w : Fin m → ℝ := fun j ↦ (z j).re
  have hproj (c : Fin m → ℝ) :
      ‖(fun j ↦ (w j : ℂ)) - (fun j ↦ (c j : ℂ))‖ ≤
        ‖z - (fun j ↦ (c j : ℂ))‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    calc
      _ = |((z - (fun l ↦ (c l : ℂ))) j).re| := by
        simp only [Pi.sub_apply, Complex.sub_re, Complex.ofReal_re, w]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖(z - (fun l ↦ (c l : ℂ))) j‖ := Complex.abs_re_le_norm _
      _ ≤ _ := norm_le_pi_norm _ j
  have hw : (fun j ↦ (w j : ℂ)) ∈ Metric.ball (fun j ↦ (a j : ℂ)) r ∩
      Metric.ball (fun j ↦ (b j : ℂ)) s := by
    constructor
    · simpa only [Metric.mem_ball, dist_eq_norm] using
        (hproj a).trans_lt (show ‖z - (fun j ↦ (a j : ℂ))‖ < r by
        simpa only [Metric.mem_ball, dist_eq_norm] using hz.1)
    · simpa only [Metric.mem_ball, dist_eq_norm] using
        (hproj b).trans_lt (show ‖z - (fun j ↦ (b j : ℂ))‖ < s by
        simpa only [Metric.mem_ball, dist_eq_norm] using hz.2)
  have hcont : Continuous (fun y : Fin m → ℝ ↦ fun j ↦ (y j : ℂ)) := by
    fun_prop
  have hn : {y : Fin m → ℝ | (fun j ↦ (y j : ℂ)) ∈
      Metric.ball (fun j ↦ (a j : ℂ)) r ∩ Metric.ball (fun j ↦ (b j : ℂ)) s} ∈ 𝓝 w :=
    hcont.continuousAt.preimage_mem_nhds
      ((Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds hw)
  have hreal : (fun y : Fin m → ℝ ↦ f (fun j ↦ (y j : ℂ))) =ᶠ[𝓝 w]
      (fun y : Fin m → ℝ ↦ h (fun j ↦ (y j : ℂ))) := by
    filter_upwards [hn] with y hy
    exact (hfG y hy.1).trans (hhG y hy.2).symm
  have he := collar_complex_real_germ_uniqueness f h w (hf _ hw.1) (hh _ hw.2) hreal
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hf.mono inter_subset_left) (hh.mono inter_subset_right)
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected hw he hz

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_extension_overlap
