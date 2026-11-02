import Smoothing.ParameterOriginalCoreBounds
import Smoothing.ParameterLocalOriginalPair

/-!
# Actual sampling-domain budgets from the unchanged original Core

Source: original repair compact-parameter-manifold clause, main.tex 686 and
778; the probes first extend their small parameter ball to a compact torus
(main.tex 877). For that route the evaluated parameter set is all of P.

The original Core and all its native fields remain unchanged. A genuine
inclusion of the fixed source and parameter sampling buffers in its original
norm domains supplies the original pair budget with factor two. The source
`inner` inclusion alone does not imply this buffer inclusion. For a proper
compact subset K, an additional actual sampling-to-K inclusion is required;
there is no claim that a K-only input controls values outside K.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold IsManifold
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Only actual set inclusions are used: neither a numeric input bound nor
compactness can enlarge an evaluation domain. -/
theorem parameterRound2_sampling_subset_core_evaluation
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P (EuclideanSpace ℝ (Fin d)))
    (hsource : ∀ i, bufferedSamplingCoordinates D.atlas i ⊆ D.sourceNormDomain i)
    (hparameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ D.parameterNormDomain i)
    (hset : ∀ i y, y ∈ tensorLocalOriginalSampling D.atlas B i →
      (incrementsOriginalJointPoint D.atlas B.chart i y).1 ∈ D.parameterSet)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    tensorLocalOriginalSampling D.atlas B i ⊆
      incrementsOriginalEvaluation D.atlas B.chart D.sourceNormDomain D.parameterNormDomain D.parameterSet i := by
  intro y hy
  exact ⟨hy.1, hsource i.1 hy.2.1, hparameter i.2 hy.2.2.1, hset i y hy⟩

/-- The full compact-parameter-manifold route takes the evaluation set to be
univ, so the parameter-set part of the sampling inclusion is automatic.
The two real coordinate-buffer inclusions remain explicit geometry. -/
theorem parameterRound2_sampling_subset_core_evaluation_univ
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P (EuclideanSpace ℝ (Fin d)))
    (hsource : ∀ i, bufferedSamplingCoordinates D.atlas i ⊆ D.sourceNormDomain i)
    (hparameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ D.parameterNormDomain i)
    (hset : D.parameterSet = univ)
    (i : Fin D.atlas.count × Fin D.parameterCount) :
    tensorLocalOriginalSampling D.atlas B i ⊆
      incrementsOriginalEvaluation D.atlas B.chart D.sourceNormDomain D.parameterNormDomain D.parameterSet i :=
  parameterRound2_sampling_subset_core_evaluation D B hsource hparameter
    (by intro i y hy; rw [hset]; exact Set.mem_univ _) i

/-- The actual local-family pair on its genuine sampling domain is bounded
by the original Core MAX with the fixed factor two. All coordinates and the
full joint base-two/base-zero norms are precisely the original ones. -/
theorem parameterRound2_sampling_pair_le_core
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P (EuclideanSpace ℝ (Fin d)))
    (hchart : B.chart = D.parameterChart)
    (hdomains : ∀ i, tensorLocalOriginalSampling D.atlas B i ⊆
      incrementsOriginalEvaluation D.atlas B.chart D.sourceNormDomain D.parameterNormDomain D.parameterSet i)
    (j : ℕ) (ell : ℝ) :
    parameterLocalOriginalTotalPairWeighted D.atlas B D.F D.H j ell
      (tensorLocalOriginalSampling D.atlas B) ≤ parameterOriginalCorePairProfile D j ell := by
  unfold parameterLocalOriginalTotalPairWeighted parameterOriginalCorePairProfile
  rw [← hchart]
  exact add_le_add
    (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hdomains)
    (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hdomains)

/-- A single genuine original Core budget supplies finiteness and the actual
pair's sampling budget, before any ENNReal-to-real conversion is used. -/
theorem parameterRound2_sampling_pair_finite_and_budget
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P (EuclideanSpace ℝ (Fin d)))
    (hchart : B.chart = D.parameterChart)
    (hdomains : ∀ i, tensorLocalOriginalSampling D.atlas B i ⊆
      incrementsOriginalEvaluation D.atlas B.chart D.sourceNormDomain D.parameterNormDomain D.parameterSet i)
    (j : ℕ) (ell : ℝ)
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile D j ell).toReal ≤ budget) :
    parameterLocalOriginalTotalPairWeighted D.atlas B D.F D.H j ell
      (tensorLocalOriginalSampling D.atlas B) ≠ ⊤ ∧
    (parameterLocalOriginalTotalPairWeighted D.atlas B D.F D.H j ell
      (tensorLocalOriginalSampling D.atlas B)).toReal ≤ 2 * budget := by
  have h := parameterOriginalCore_pair_finite_and_budget D j ell hfinite budget hbudget
  have hle := parameterRound2_sampling_pair_le_core D B hchart hdomains j ell
  exact ⟨ne_top_of_le_ne_top h.1 hle, (ENNReal.toReal_mono h.1 hle).trans h.2⟩

/-- True C2-map/C0-tensor inputs for the SAME smoother are already below the
sampling weighted pair. No extra derivative budget is added. -/
theorem parameterRound2_sampling_base_pair_le_weighted
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P (EuclideanSpace ℝ (Fin d)))
    (j : ℕ) (ell : ℝ) :
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates D.atlas B.chart D.F)
      (incrementsOriginalDifferentiation D.atlas B.chart) (tensorLocalOriginalSampling D.atlas B) +
    paperAtlasCj 0 (incrementsOriginalTensorCoordinates D.atlas B.chart D.H)
      (incrementsOriginalDifferentiation D.atlas B.chart) (tensorLocalOriginalSampling D.atlas B)) ≤
    parameterLocalOriginalTotalPairWeighted D.atlas B D.F D.H j ell
      (tensorLocalOriginalSampling D.atlas B) :=
  add_le_add (parameterPaperAtlasCj_base_le_weighted 2 j ell _ _ _)
    (parameterPaperAtlasCj_base_le_weighted 0 j ell _ _ _)

/-- The original Core supplies the true low-order pair gain input on the
actual sampling buffers, with one fixed factor two and genuine finiteness. -/
theorem parameterRound2_sampling_base_pair_finite_and_budget
    (D : IncrementsOriginalNativeData n d N M P)
    (B : TensorBufferedChartFamily (Fin D.parameterCount) P (EuclideanSpace ℝ (Fin d)))
    (hchart : B.chart = D.parameterChart)
    (hdomains : ∀ i, tensorLocalOriginalSampling D.atlas B i ⊆
      incrementsOriginalEvaluation D.atlas B.chart D.sourceNormDomain D.parameterNormDomain D.parameterSet i)
    (j : ℕ) (ell : ℝ)
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile D j ell).toReal ≤ budget) :
    let G := paperAtlasCj 2 (incrementsOriginalMapCoordinates D.atlas B.chart D.F)
      (incrementsOriginalDifferentiation D.atlas B.chart) (tensorLocalOriginalSampling D.atlas B)
    let H := paperAtlasCj 0 (incrementsOriginalTensorCoordinates D.atlas B.chart D.H)
      (incrementsOriginalDifferentiation D.atlas B.chart) (tensorLocalOriginalSampling D.atlas B)
    G + H ≠ ⊤ ∧ (G + H).toReal ≤ 2 * budget := by
  dsimp only
  have h := parameterRound2_sampling_pair_finite_and_budget D B hchart hdomains j ell hfinite budget hbudget
  have hle := parameterRound2_sampling_base_pair_le_weighted D B j ell
  exact ⟨ne_top_of_le_ne_top h.1 hle, (ENNReal.toReal_mono h.1 hle).trans h.2⟩

#print axioms parameterRound2_sampling_pair_finite_and_budget
#print axioms parameterRound2_sampling_base_pair_finite_and_budget
#print axioms parameterRound2_sampling_subset_core_evaluation_univ
end
end GlobalEmbedding.Continuation
