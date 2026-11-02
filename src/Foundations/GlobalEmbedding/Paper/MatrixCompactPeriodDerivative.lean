import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Differentiating an actual compact-period integral

Source: `main.tex`, `prop:matrix`, lines307–365.
DAG: `matrix-compact-period-derivative`.
This is the dimension-independent public version of the compact domination
argument already used for the four angle coefficients. It applies also to
scalar-moment and continuous-linear-map-valued derivative families.
-/

open Set Filter MeasureTheory Metric
open scoped Topology

namespace GlobalEmbedding.Paper

/-- Jointly continuous actual coefficient integrands and actual derivatives
permit genuine differentiation through the compact-period integral.

Proof: continuity bounds the actual derivative on the compact closed unit
coefficient ball times [0,1]. This constant is an integrable dominating bound.
Apply Mathlib's actual dominated Frechet differentiation theorem, with all
measurability and integrability supplied by continuity on the compact period.
Source: `prop:matrix`, the actual derivative-Gram calculation, lines307–365. -/
theorem hasFDerivAt_compact_period
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E × ℝ → F) (g : E × ℝ → E →L[ℝ] F)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ a t, HasFDerivAt (fun b ↦ f (b, t)) (g (a, t)) a) (a : E) :
    HasFDerivAt (fun b ↦ ∫ t in Icc (0 : ℝ) 1, f (b, t))
      (∫ t in Icc (0 : ℝ) 1, g (a, t)) a := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall a (1 : ℝ)).prod isCompact_Icc)
    |>.exists_bound_of_continuousOn hg.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (s := ball a 1) (bound := fun _ ↦ B) (ball_mem_nhds a zero_lt_one)
  · exact .of_forall fun b ↦
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn.aestronglyMeasurable
        measurableSet_Icc
  · exact (hf.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
  · exact (hg.comp (continuous_const.prodMk continuous_id)).continuousOn.aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht b hb
    exact hB (b, t) ⟨ball_subset_closedBall hb, ht⟩
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · exact .of_forall fun t b _ ↦ hd b t

#print axioms hasFDerivAt_compact_period

end GlobalEmbedding.Paper
