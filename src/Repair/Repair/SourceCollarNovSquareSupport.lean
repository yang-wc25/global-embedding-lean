import Probes.Round4RefinementSquareCutoffs

/-!
The fixed positive denominator of the existing square normalization preserves
ordinary and topological support exactly.  Consequently two normalized bump
families with the same radius and center have exactly the same support,
independently of all their other centers.  This lets the original local normal
factory be used center by center without altering the final global cutoffs.
-/

noncomputable section
open GlobalEmbedding.Offline Set Function Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

 theorem sourceCollarNov_normalized_support {ι X : Type*} [Fintype ι]
    (raw : ι → X → ℝ) (i : ι) :
    Function.support (tensorLocalNormalizedCutoff raw i) = Function.support (raw i) := by
  ext x
  have hpos : 0 < reciprocalSquareRoot (squareCutoffSum (tensorLocalAugmentedRaw raw) x) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le (tensorLocalAugmentedRaw_one_le raw x)) _
  simp only [Function.mem_support, tensorLocalNormalizedCutoff, squareNormalizedCutoff,
    tensorLocalAugmentedRaw, mul_ne_zero_iff, ne_eq]
  exact and_iff_left (ne_of_gt hpos) |>.trans (and_iff_right (by norm_num : (2 : ℝ) ≠ 0))

theorem sourceCollarNov_normalized_tsupport {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (raw : ι → X → ℝ) (i : ι) :
    tsupport (tensorLocalNormalizedCutoff raw i) = tsupport (raw i) := by
  change closure (Function.support (tensorLocalNormalizedCutoff raw i)) = closure (Function.support (raw i))
  rw [sourceCollarNov_normalized_support]

theorem sourceCollarNov_square_tsupport (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (r : ℝ) (hr : 0 < r) (z : s) :
    tsupport (round4RefinementSquareCutoff E s r z) = closedBall z.val (2*r) := by
  rw [round4RefinementSquareCutoff, sourceCollarNov_normalized_tsupport,
    actualRefinementBump_tsupport E r hr z.val]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_square_tsupport
