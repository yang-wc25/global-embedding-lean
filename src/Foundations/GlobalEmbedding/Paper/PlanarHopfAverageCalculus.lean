import GlobalEmbedding.Paper.PlanarHopfFlow
import Mathlib.Geometry.Manifold.Algebra.Structures
import GlobalEmbedding.Paper.MatrixManifoldCompactParameterIntegral
import GlobalEmbedding.Paper.MatrixPeriodicAverageInvariance
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Native calculus of the actual Hopf period average

Source: `main.tex`, `prop:matrix`, lines293–366.
DAG: `planar-hopf-average-calculus`.
These are thin applications of the accepted actual compact integral and period
invariance theorems to the actual period-one native Hopf flow.
-/

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The actual Hopf average is native smooth, by the accepted compact-parameter
integral theorem and actual joint smoothness of the Hopf flow.
Source: `prop:matrix`, lines307–366. -/
theorem planarHopfAverage_contMDiff {C : ℕ} [Fact (0 < C)]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : PlanarHopfSphere C → E)
    (hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ u) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, E) ∞ (orbitAverage planarHopfFlow u) := by
  have hR : ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, ℝ)) (planarHopfModel C) ∞
      (fun p : PlanarHopfSphere C × ℝ ↦ planarHopfFlow p.2 p.1) :=
    (planarHopfFlow_contMDiff C).comp (contMDiff_snd.prodMk contMDiff_fst)
  have hI := contMDiff_compact_parameter_integral (⊤ : ℕ∞) _ (hu.comp hR)
  apply hI.congr
  intro z
  unfold orbitAverage
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Icc_eq_integral_Ioc]
  rfl

/-- The literal Hopf period average is invariant under every actual orbit shift.
Proof: apply the accepted period-one average theorem and identify interval and
closed-interval integrals. Source: `prop:matrix`, lines307–366. -/
theorem planarHopfAverage_flow {C : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : PlanarHopfSphere C → E) (z : PlanarHopfSphere C) (s : ℝ) :
    orbitAverage planarHopfFlow u (planarHopfFlow s z) = orbitAverage planarHopfFlow u z := by
  unfold orbitAverage
  simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Icc_eq_integral_Ioc] using
    periodic_average_invariant planarHopfFlow planarHopfFlow_add planarHopfFlow_one u z s

/-- The actual flat cutoff has positive actual period average when curvature is
nonzero somewhere on every orbit.

Proof: shift to an actual nonzero-curvature point. The continuous nonnegative
cutoff is strictly positive at time zero, so its integral over the period is
positive. Actual period-average invariance returns to the original point.
Source: `prop:matrix`, definition of η_b, line355. -/
theorem planarHopfAverage_cutoff_pos {C : ℕ} [Fact (0 < C)]
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hn : ∀ z, ∃ s : ℝ, κ (planarHopfFlow s z) ≠ 0) (z : PlanarHopfSphere C) :
    0 < orbitAverage planarHopfFlow (fun w ↦ expNegInvGlue (κ w ^ 2)) z := by
  obtain ⟨s, hs⟩ := hn z
  let u : PlanarHopfSphere C → ℝ := fun w ↦ expNegInvGlue (κ w ^ 2)
  have hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u :=
    expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t (planarHopfFlow s z)) :=
    (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
  have hp : 0 < orbitAverage planarHopfFlow u (planarHopfFlow s z) := by
    unfold orbitAverage
    exact intervalIntegral.integral_pos (by norm_num) (hu.continuous.comp hR).continuousOn
      (fun t _ ↦ expNegInvGlue.nonneg _) ⟨0, by norm_num, by
        dsimp [u]
        rw [planarHopfFlow_zero]
        exact expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero hs)⟩
  simpa only [planarHopfAverage_flow] using hp

#print axioms planarHopfAverage_contMDiff
#print axioms planarHopfAverage_flow
#print axioms planarHopfAverage_cutoff_pos

end GlobalEmbedding.Paper
