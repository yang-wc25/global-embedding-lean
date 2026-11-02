import GlobalEmbedding.Paper.PlanarOrbitPrimitive
import GlobalEmbedding.Paper.CollarCauchyKovalevskayaAnalyticODE
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual analytic norm and periodic primitive calculus

Source: `main.tex`, `lem:planar`, lines 261–262.
The norm is obtained from the actual inner product and the positive analytic
inverse of squaring; the primitive will reuse the accepted convergent primitive.
-/

open Set Filter
open scoped Topology InnerProductSpace

namespace GlobalEmbedding.Paper

/-- The actual positive square root is analytic at every positive real point,
by the native analytic inverse theorem applied to squaring. -/
theorem planar_analyticAt_sqrt {a : ℝ} (ha : 0 < a) : AnalyticAt ℝ Real.sqrt a := by
  let b := Real.sqrt a
  have hb : 0 < b := Real.sqrt_pos.mpr ha
  have hs : AnalyticAt ℝ (fun y : ℝ ↦ y ^ 2) b := analyticAt_id.pow 2
  have hd : deriv (fun y : ℝ ↦ y ^ 2) b ≠ 0 := by
    rw [(hasDerivAt_pow 2 b).deriv]
    positivity
  have he : (id : ℝ → ℝ) =ᶠ[𝓝 b] Real.sqrt ∘ (fun y : ℝ ↦ y ^ 2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hb] with y hy
    exact (Real.sqrt_sq (le_of_lt hy)).symm
  have hcomp : AnalyticAt ℝ (Real.sqrt ∘ (fun y : ℝ ↦ y ^ 2)) b :=
    analyticAt_id.congr he
  have hh := (analyticAt_comp_iff_of_deriv_ne_zero hs hd).mp hcomp
  simpa only [b, Real.sq_sqrt ha.le] using hh

/-- The genuine norm of a nonvanishing analytic real inner-product curve is analytic. -/
theorem planar_analyticAt_norm_curve
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {v : ℝ → F} {s : ℝ} (hv : AnalyticAt ℝ v s) (hn : v s ≠ 0) :
    AnalyticAt ℝ (fun t ↦ ‖v t‖) s := by
  have hi : AnalyticAt ℝ (fun t ↦ ⟪v t, v t⟫_ℝ) s :=
    ((innerSL ℝ (E := F)).analyticAt_bilinear (v s, v s)).comp
      (f := fun t ↦ (v t, v t)) (hv.prod hv)
  have hp : 0 < ⟪v s, v s⟫_ℝ := real_inner_self_pos.mpr hn
  have hh : AnalyticAt ℝ (fun t ↦ Real.sqrt ⟪v t, v t⟫_ℝ) s :=
    (planar_analyticAt_sqrt hp).comp (f := fun t ↦ ⟪v t, v t⟫_ℝ) hi
  simpa only [Function.comp_def, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using hh

/-- Analyticity follows from an actual analytic derivative germ: the accepted
convergent primitive differs from the actual function by a genuine local constant. -/
theorem planar_analyticAt_zero_of_hasDerivAt {f u : ℝ → ℝ}
    (hu : AnalyticAt ℝ u 0) (hf : ∀ᶠ t in 𝓝 0, HasDerivAt f (u t) t) :
    AnalyticAt ℝ f 0 := by
  obtain ⟨P, hP0, hP, hdP⟩ := collar_analytic_primitive_at_zero hu
  obtain ⟨ε, hε, hd⟩ := Metric.eventually_nhds_iff_ball.mp (hf.and hdP)
  have he : Set.EqOn f (fun t ↦ P t + f 0) (Metric.ball 0 ε) := by
    apply Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℝ) ε).isPreconnected
      (fun t ht ↦ (hd t ht).1.differentiableAt.differentiableWithinAt)
      (fun t ht ↦ ((hd t ht).2.add_const (f 0)).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ ?_) (Metric.mem_ball_self hε) (by simp [hP0])
    exact (hd t ht).1.deriv.trans ((hd t ht).2.add_const (f 0)).deriv.symm
  exact (hP.add analyticAt_const).congr
    (eventually_of_mem (Metric.ball_mem_nhds 0 hε) (fun t ht ↦ (he ht).symm))

/-- The preceding actual derivative-germ argument at an arbitrary real time. -/
theorem planar_analyticAt_of_hasDerivAt {f u : ℝ → ℝ} {s : ℝ}
    (hu : AnalyticAt ℝ u s) (hf : ∀ᶠ t in 𝓝 s, HasDerivAt f (u t) t) :
    AnalyticAt ℝ f s := by
  have hua : AnalyticAt ℝ (fun t : ℝ ↦ u (s + t)) 0 := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq] using hu.comp_of_eq
      (analyticAt_const.add analyticAt_id) (add_zero s)
  have hfd : ∀ᶠ t in 𝓝 0, HasDerivAt (fun t : ℝ ↦ f (s + t)) (u (s + t)) t := by
    have ht : Filter.Tendsto (fun t : ℝ ↦ s + t) (𝓝 0) (𝓝 s) := by
      simpa only [add_zero] using
        (show Continuous (fun t : ℝ ↦ s + t) from continuous_const.add continuous_id).tendsto 0
    filter_upwards [ht.eventually hf] with t hd
    simpa only [Function.comp_def, zero_add, one_smul] using
      hd.scomp t ((hasDerivAt_const t s).add (hasDerivAt_id t))
  have ha := planar_analyticAt_zero_of_hasDerivAt hua hfd
  have hh : AnalyticAt ℝ (fun t : ℝ ↦ f (s + (t - s))) s := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq] using ha.comp_of_eq
      (analyticAt_id.sub analyticAt_const) (sub_self s)
  simpa only [sub_eq_add_neg, add_left_comm s _ (-s), add_neg_cancel, add_zero] using hh

/-- The literal weighted primitive is analytic along an actual period-one orbit.
Its actual derivative is the analytic observable minus its genuine period mean. -/
theorem planarOrbitPrimitive_orbit_analytic {Q : Type*}
    (R : ℝ → Q → Q) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (u : Q → ℝ) (z : Q)
    (hu : AnalyticOnNhd ℝ (fun s : ℝ ↦ u (R s z)) Set.univ) :
    AnalyticOnNhd ℝ (fun s : ℝ ↦ planarOrbitPrimitive R u (R s z)) Set.univ := by
  have hc : Continuous (fun s : ℝ ↦ u (R s z)) :=
    continuous_iff_continuousAt.mpr (fun s ↦ (hu s (mem_univ s)).continuousAt)
  intro s _
  apply planar_analyticAt_of_hasDerivAt
    ((hu s (mem_univ s)).sub (analyticAt_const (v := orbitAverage R u z)))
  apply Filter.Eventually.of_forall
  intro y
  have hd := planarPeriodicPrimitive_hasDerivAt (fun t : ℝ ↦ u (R t z)) hc
    (orbitMap_periodic R hadd hone u z) y
  simpa only [planarOrbitPrimitive, ← hadd, orbitAverage, Pi.sub_apply] using hd

#print axioms planarOrbitPrimitive_orbit_analytic
#print axioms planar_analyticAt_of_hasDerivAt
#print axioms planar_analyticAt_sqrt
#print axioms planar_analyticAt_norm_curve

end GlobalEmbedding.Paper
