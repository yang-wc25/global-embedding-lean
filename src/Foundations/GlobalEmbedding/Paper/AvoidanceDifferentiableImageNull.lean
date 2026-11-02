import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Nullity of lower-dimensional differentiable images

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:avoidance`, lines 940–941.
This is the whole-chart version of the source's compact-cube Lipschitz argument, using Mathlib's
Hausdorff-dimension theorem, whose proof already supplies a countable Lipschitz cover.
DAG node: `avoidance-differentiable-image-null`.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- A differentiable map from any subset of a lower-dimensional real normed space has null
Lebesgue image. Source: `lem:avoidance`, lines 940–941. Differentiability does not increase
Hausdorff dimension, the domain has dimension at most its real finrank, and target Hausdorff
measure in its full dimension equals Lebesgue volume. No measurability, openness or convexity
of the domain set is required, and the zero-dimensional domain is included. -/
theorem avoidance_differentiable_image_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p : ℕ} (hdp : Module.finrank ℝ E < p) (s : Set E) (f : E → Fin p → ℝ)
    (hf : DifferentiableOn ℝ f s) : volume (f '' s) = 0 := by
  have hdim : dimH (f '' s) ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
    calc
      dimH (f '' s) ≤ dimH s := hf.dimH_image_le
      _ ≤ dimH (Set.univ : Set E) := dimH_mono (Set.subset_univ s)
      _ = Module.finrank ℝ E := Real.dimH_univ_eq_finrank E
  have hlt : dimH (f '' s) < (p : ℝ≥0) :=
    hdim.trans_lt (by exact_mod_cast hdp)
  have hnull := hausdorffMeasure_of_dimH_lt hlt
  rw [← hausdorffMeasure_pi_real (ι := Fin p), Fintype.card_fin]
  exact hnull

#print axioms avoidance_differentiable_image_null

end GlobalEmbedding.Paper
