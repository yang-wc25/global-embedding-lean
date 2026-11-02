import Smoothing.TensorPreparedProduct
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Actual smooth square cutoffs from a cover only near the parameter set

A finite raw family need not cover the whole parameter manifold. To normalize
it, scale the genuine raw functions by two and add one fixed scalar bump of
their actual square sum to the denominator. The extra scalar is NOT an atlas
chart and does not enter the smoother. It vanishes on a neighborhood of every
point having an original unit plateau. Thus the original finite family has
sum of squares exactly one there, is globally smooth, and retains its supports.

This removes the global-cover requirement for cutoff normalization itself;
it does not claim that the existing global BufferedAtlas estimates have already
been generalized to a parameter chart family without a global cover.
-/

open Manifold IsManifold Function Set
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A fixed real bump, equal to one on [-1,1] and zero outside (-2,2). -/
def tensorCoverageBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

variable {ι X : Type*} [Fintype ι]

def tensorLocalCoverageSum (b : ι → X → ℝ) : X → ℝ :=
  squareCutoffSum (fun i x => 2 * b i x)

/-- The extra scalar repairs only the normalization denominator. -/
def tensorLocalAugmentedRaw (b : ι → X → ℝ) : Option ι → X → ℝ
  | none => tensorCoverageBump ∘ tensorLocalCoverageSum b
  | some i => fun x => 2 * b i x

/-- Only the ORIGINAL indices are retained in the actual cutoff family. -/
def tensorLocalNormalizedCutoff (b : ι → X → ℝ) (i : ι) : X → ℝ :=
  squareNormalizedCutoff (tensorLocalAugmentedRaw b) (some i)

theorem tensorLocalCoverageSum_nonneg (b : ι → X → ℝ) (x : X) :
    0 ≤ tensorLocalCoverageSum b x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem tensorLocalAugmentedRaw_square_sum (b : ι → X → ℝ) (x : X) :
    squareCutoffSum (tensorLocalAugmentedRaw b) x =
      tensorCoverageBump (tensorLocalCoverageSum b x) ^ 2 + tensorLocalCoverageSum b x := by
  simp only [squareCutoffSum, Fintype.sum_option, tensorLocalAugmentedRaw,
    Function.comp_apply, tensorLocalCoverageSum]

/-- The ACTUAL denominator is uniformly bounded below by one everywhere,
including points at which every original raw cutoff vanishes. -/
theorem tensorLocalAugmentedRaw_one_le (b : ι → X → ℝ) (x : X) :
    1 ≤ squareCutoffSum (tensorLocalAugmentedRaw b) x := by
  rw [tensorLocalAugmentedRaw_square_sum]
  have hs := tensorLocalCoverageSum_nonneg b x
  by_cases h : tensorLocalCoverageSum b x ≤ 1
  · have hb : tensorCoverageBump (tensorLocalCoverageSum b x) = 1 :=
      tensorCoverageBump.one_of_mem_closedBall (by
        simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
          abs_of_nonneg hs, tensorCoverageBump] using h)
    rw [hb, one_pow]
    linarith
  · linarith [sq_nonneg (tensorCoverageBump (tensorLocalCoverageSum b x))]

/-- The extra scalar vanishes once the genuine raw square sum exceeds two. -/
theorem tensorLocalNormalizedCutoff_square_sum (b : ι → X → ℝ) (x : X)
    (hx : 2 ≤ tensorLocalCoverageSum b x) :
    ∑ i, tensorLocalNormalizedCutoff b i x ^ 2 = 1 := by
  have hb : tensorCoverageBump (tensorLocalCoverageSum b x) = 0 :=
    tensorCoverageBump.zero_of_le_dist (by
      simpa only [tensorCoverageBump, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (tensorLocalCoverageSum_nonneg b x)] using hx)
  have hn : squareNormalizedCutoff (tensorLocalAugmentedRaw b) none x = 0 := by
    simp only [squareNormalizedCutoff, tensorLocalAugmentedRaw, Function.comp_apply, hb, zero_mul]
  have h := squareNormalizedCutoff_sum_sq (tensorLocalAugmentedRaw b) x
    (zero_lt_one.trans_le (tensorLocalAugmentedRaw_one_le b x))
  simpa only [Fintype.sum_option, hn, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    tensorLocalNormalizedCutoff] using h

/-- A unit plateau at a point gives a strict reserve, hence a neighborhood
on which the actual square partition is one. No cover away from this point is used. -/
theorem tensorLocalCoverageSum_four_le (b : ι → X → ℝ) (x : X)
    (hx : ∃ i, b i x = 1) : 4 ≤ tensorLocalCoverageSum b x := by
  obtain ⟨i, hi⟩ := hx
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun j => (2 * b j x) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  norm_num only [hi, mul_one] at h
  exact h

variable [TopologicalSpace X]

theorem tensorLocalNormalizedCutoff_tsupport_subset (b : ι → X → ℝ) (i : ι) :
    tsupport (tensorLocalNormalizedCutoff b i) ⊆ tsupport (b i) :=
  (squareNormalizedCutoff_tsupport_subset (tensorLocalAugmentedRaw b) (some i)).trans
    tsupport_mul_subset_right

/-- The extra scalar creates NO additional active chart index. -/
theorem tensorLocalNormalizedCutoff_card_le (b : ι → X → ℝ) (x : X) :
    (activeCutoffIndices (tensorLocalNormalizedCutoff b) x).card ≤
      (activeCutoffIndices b x).card := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact (mem_activeCutoffIndices b x i).mpr (tensorLocalNormalizedCutoff_tsupport_subset b i
    ((mem_activeCutoffIndices _ x i).mp hi))

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H X]

theorem tensorLocalCoverageSum_contMDiff (b : ι → X → ℝ)
    (hb : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (b i)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (tensorLocalCoverageSum b) := by
  apply ContMDiff.sum
  intro i _
  exact (contDiff_id.pow 2).comp_contMDiff (contMDiff_const.mul (hb i))

/-- Global smoothness holds even though the raw family covers only the
stated compact parameter region. No chart or plateau is added outside it. -/
theorem tensorLocalNormalizedCutoff_contMDiff (b : ι → X → ℝ)
    (hb : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (b i)) (i : ι) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (tensorLocalNormalizedCutoff b i) := by
  apply squareNormalizedCutoff_contMDiff (tensorLocalAugmentedRaw b) _
    (tensorLocalAugmentedRaw_one_le b) (some i)
  intro a
  cases a with
  | none => exact tensorCoverageBump.contDiff.comp_contMDiff (tensorLocalCoverageSum_contMDiff b hb)
  | some j => exact contMDiff_const.mul (hb j)

/-- A true open neighborhood of the specified parameter set carries the
same exact square partition. Compactness is not needed for this algebraic step. -/
theorem tensorLocalNormalizedCutoff_partition_near
    (b : ι → X → ℝ) (hb : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (b i))
    (K : Set X) (hcover : ∀ x ∈ K, ∃ i, b i x = 1) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∀ x ∈ U, ∑ i, tensorLocalNormalizedCutoff b i x ^ 2 = 1 := by
  refine ⟨{x | 2 < tensorLocalCoverageSum b x},
    isOpen_lt continuous_const (tensorLocalCoverageSum_contMDiff b hb).continuous, ?_, ?_⟩
  · intro x hx
    exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < 4) (tensorLocalCoverageSum_four_le b x (hcover x hx))
  · intro x hx
    exact tensorLocalNormalizedCutoff_square_sum b x hx.le

end
end GlobalEmbedding.Offline
