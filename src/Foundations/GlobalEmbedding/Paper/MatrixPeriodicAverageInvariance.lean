import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Orbit invariance of the actual period-one average

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines 307–315.
DAG node: `matrix-periodic-average-invariance`.
-/

open Set MeasureTheory

namespace GlobalEmbedding.Paper

/-- The actual compact-period average is invariant under a period-one real action.

Proof: the action/period laws make the actual integrand one-periodic. The action law
rewrites the average at R_u(q) as the time-translated integrand average. Endpoints have
zero volume, so use interval integration, translation of the interval, and Mathlib's
actual one-period integral independence theorem. Source: `prop:matrix`, lines 307–315. -/
theorem periodic_average_invariant
    {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (hadd : ∀ s t q, R (s + t) q = R s (R t q))
    (hperiod : ∀ q, R 1 q = q) (g : Q → E) (q : Q) (u : ℝ) :
    (∫ t in Icc (0 : ℝ) 1, g (R t (R u q))) = ∫ t in Icc (0 : ℝ) 1, g (R t q) := by
  let f : ℝ → E := fun t ↦ g (R t q)
  have hf : Function.Periodic f 1 := by
    intro t
    simp only [f, hadd, hperiod]
  have hshift : (fun t ↦ g (R t (R u q))) = (fun t ↦ f (t + u)) := by
    funext t
    exact congrArg g (hadd t u q).symm
  rw [hshift, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm 1 u] using hf.intervalIntegral_add_eq u 0

#print axioms periodic_average_invariant

end GlobalEmbedding.Paper
