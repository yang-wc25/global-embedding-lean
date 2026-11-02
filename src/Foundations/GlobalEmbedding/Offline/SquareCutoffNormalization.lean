import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Support

/-!
# Actual square normalization with uniform derivatives at every order

Source: `literature/parallelizable-stable-plus-one/main.tex`, the colored square
partition in `prop:initialization`, and original node
`initialization-colored-cutoffs-square-partition-normalization`.

All derivative estimates use native actual `iteratedFDeriv`, the native
Faà di Bruno bound for composition, and the native product rule. The input
square-sum bounds are the separate original bounded-overlap/transition provider;
they are not asserted to have been constructed here.

This is an isolated offline candidate, not a main-library acceptance receipt.
-/

noncomputable section

open Function Filter Manifold IsManifold Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

/-- The literal positive-power function used in square normalization. -/
def reciprocalSquareRoot (s : ℝ) : ℝ := s ^ (-(1 / 2) : ℝ)

/-- The actual reciprocal square root is smooth on the positive half-line.
Proof: native smoothness of a real power away from zero.
Source: the square-normalization node. -/
theorem reciprocalSquareRoot_contDiffOn :
    ContDiffOn ℝ ∞ reciprocalSquareRoot (Set.Ioi 0) := by
  exact contDiffOn_id.rpow_const_of_ne (fun x hx ↦ ne_of_gt hx)

/-- The actual finite sum of squared pre-cutoffs. -/
def squareCutoffSum {ι X : Type*} [Fintype ι] (b : ι → X → ℝ) : X → ℝ :=
  fun x ↦ ∑ i, b i x ^ 2

/-- The literal normalized cutoff `b_i * (sum_j b_j^2)^(-1/2)`. -/
def squareNormalizedCutoff {ι X : Type*} [Fintype ι] (b : ι → X → ℝ) (i : ι) : X → ℝ :=
  fun x ↦ b i x * reciprocalSquareRoot (squareCutoffSum b x)

/-- A genuine unit plateau in the covering family makes its actual square sum
at least one. Proof: retain that term in a sum of nonnegative squares.
Source: the positivity step of the bounded-square-sum node. -/
theorem one_le_squareCutoffSum_of_plateau {ι X : Type*} [Fintype ι]
    (b : ι → X → ℝ) (x : X) (hcover : ∃ i, b i x = 1) :
    1 ≤ squareCutoffSum b x := by
  obtain ⟨i, hi⟩ := hcover
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ b j x ^ 2)
    (fun j _ ↦ sq_nonneg (b j x)) (Finset.mem_univ i)
  simpa only [squareCutoffSum, hi, one_pow] using h

/-- Actual square normalization gives the exact unit sum, on every point with
positive square sum. Proof: the native real-power law makes the squared factor
the reciprocal of the same square sum. Source: the square-normalization node. -/
theorem squareNormalizedCutoff_sum_sq {ι X : Type*} [Fintype ι]
    (b : ι → X → ℝ) (x : X) (hpos : 0 < squareCutoffSum b x) :
    ∑ i, squareNormalizedCutoff b i x ^ 2 = 1 := by
  have hrec : reciprocalSquareRoot (squareCutoffSum b x) ^ 2 = (squareCutoffSum b x)⁻¹ := by
    unfold reciprocalSquareRoot
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num [Real.rpow_neg_one]
  calc
    ∑ i, squareNormalizedCutoff b i x ^ 2 =
        squareCutoffSum b x * reciprocalSquareRoot (squareCutoffSum b x) ^ 2 := by
      simp only [squareNormalizedCutoff, mul_pow, squareCutoffSum, Finset.sum_mul]
    _ = 1 := by rw [hrec, mul_inv_cancel₀ hpos.ne']

/-- Normalization never enlarges the ordinary support, independently of all
smoothness and lower-bound hypotheses. Source: the square-normalization node. -/
theorem squareNormalizedCutoff_support_subset {ι X : Type*} [Fintype ι]
    (b : ι → X → ℝ) (i : ι) :
    Function.support (squareNormalizedCutoff b i) ⊆ Function.support (b i) :=
  Function.support_mul_subset_left _ _

/-- The same support preservation holds for the actual topological support.
Source: compact containment after square normalization. -/
theorem squareNormalizedCutoff_tsupport_subset {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (b : ι → X → ℝ) (i : ι) : tsupport (squareNormalizedCutoff b i) ⊆ tsupport (b i) :=
  tsupport_mul_subset_left

/-- The actual derivatives of the reciprocal square root through every fixed
order have one common bound on the fixed compact interval `[1,max(1,C0)]`.

Proof: all its actual iterated derivatives are continuous on the positive
half-line. Native compact-image boundedness bounds each order on the interval;
a finite sum of nonnegative bounds bounds all orders through `j`.
Source: the repeated-chain-rule estimate in the square-normalization node. -/
theorem exists_reciprocalSquareRoot_derivative_bounds (C0 : ℝ) :
    ∃ R : ℕ → ℝ, (∀ j, 0 ≤ R j) ∧
      ∀ j i, i ≤ j → ∀ s ∈ Set.Icc 1 (max 1 C0),
        ‖iteratedFDeriv ℝ i reciprocalSquareRoot s‖ ≤ R j := by
  have hbound (i : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ s ∈ Set.Icc 1 (max 1 C0), ‖iteratedFDeriv ℝ i reciprocalSquareRoot s‖ ≤ A := by
    have hcont : ContinuousOn (fun s ↦ ‖iteratedFDeriv ℝ i reciprocalSquareRoot s‖)
        (Set.Icc 1 (max 1 C0)) :=
      ((ContinuousOn.continuousOn_iteratedFDeriv reciprocalSquareRoot_contDiffOn
        isOpen_Ioi (by simp)).norm).mono (fun s hs ↦ lt_of_lt_of_le zero_lt_one hs.1)
    obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) (max 1 C0))).bddAbove_image hcont
    exact ⟨max 0 A, le_max_left _ _, fun s hs ↦ (hA ⟨s, hs, rfl⟩).trans (le_max_right _ _)⟩
  choose A hApos hA using hbound
  refine ⟨fun j ↦ ∑ i ∈ Finset.range (j + 1), A i,
    fun j ↦ Finset.sum_nonneg (fun i _ ↦ hApos i), ?_⟩
  intro j i hij s hs
  exact (hA i s hs).trans
    (Finset.single_le_sum (fun k _ ↦ hApos k) (by simpa using hij))

section CoordinateBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual derivative bounds `C_i*K^i` on a positive function with `S≥1` imply
actual derivative bounds `R_j*K^j` for its reciprocal square root, with `R`
chosen BEFORE the scale, function, open chart domain, or point.

Proof: the order-zero input confines `S` to the fixed compact scalar interval.
For each `j`, set `A_j=1+sum_{i≤j} C_i`. For `1≤i≤j`, the actual `i`-th
derivative of `S` is at most `(A_j*K)^i`. Invoke the existing native composition
bound, with the preceding actual derivative bounds of the reciprocal square
root, obtaining `j! * R_j * A_j^j * K^j`. Open chart domains ensure all native
within derivatives agree with actual full derivatives there.
Source: the ALL-order chain-rule step of square normalization. -/
theorem exists_reciprocalSquareRoot_composition_bounds
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) :
    ∃ R : ℕ → ℝ, (∀ j, 0 ≤ R j) ∧
      ∀ (K : ℝ), 1 ≤ K → ∀ (S : E → ℝ) (O : Set E), IsOpen O →
      ContDiffOn ℝ ∞ S O → (∀ x ∈ O, 1 ≤ S x) →
      (∀ j, ∀ x ∈ O, ‖iteratedFDeriv ℝ j S x‖ ≤ C j * K ^ j) →
      ∀ j, ∀ x ∈ O,
        ‖iteratedFDeriv ℝ j (reciprocalSquareRoot ∘ S) x‖ ≤ R j * K ^ j := by
  obtain ⟨R0, hR0, houter⟩ := exists_reciprocalSquareRoot_derivative_bounds (C 0)
  let A : ℕ → ℝ := fun j ↦ 1 + ∑ i ∈ Finset.range (j + 1), C i
  have hAone (j : ℕ) : 1 ≤ A j := by
    dsimp only [A]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (j + 1)) ↦ hC i)]
  have hCA (j i : ℕ) (hij : i ≤ j) : C i ≤ A j := by
    have hsum : C i ≤ ∑ k ∈ Finset.range (j + 1), C k :=
      Finset.single_le_sum (fun k _ ↦ hC k) (by simpa using hij)
    dsimp only [A]
    linarith
  refine ⟨fun j ↦ (j.factorial : ℝ) * R0 j * (A j) ^ j,
    fun j ↦ mul_nonneg (mul_nonneg (by positivity) (hR0 j))
      (pow_nonneg ((zero_le_one.trans (hAone j))) j), ?_⟩
  intro K hK S O hO hS hSpos hSbound j x hx
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hxpos : 0 < S x := lt_of_lt_of_le zero_lt_one (hSpos x hx)
  have hxupper : S x ≤ max 1 (C 0) := by
    have hzero := hSbound 0 x hx
    simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos hxpos] at hzero
    exact hzero.trans (le_max_right 1 (C 0))
  have hout (i : ℕ) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i reciprocalSquareRoot (Set.Ioi 0) (S x)‖ ≤ R0 j := by
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hxpos]
    exact houter j i hij (S x) ⟨hSpos x hx, hxupper⟩
  have hin (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i S O x‖ ≤ (A j * K) ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hO hx]
    calc
      ‖iteratedFDeriv ℝ i S x‖ ≤ C i * K ^ i := hSbound i x hx
      _ ≤ (A j) ^ i * K ^ i := mul_le_mul_of_nonneg_right
        ((hCA j i hij).trans (le_self_pow₀ (hAone j) (by omega))) (by positivity)
      _ = (A j * K) ^ i := (mul_pow _ _ _).symm
  have hcomp := norm_iteratedFDerivWithin_comp_le reciprocalSquareRoot_contDiffOn hS
    (n := j) (by simp) isOpen_Ioi.uniqueDiffOn hO.uniqueDiffOn
    (fun y hy ↦ lt_of_lt_of_le zero_lt_one (hSpos y hy)) hx hout hin
  rw [iteratedFDerivWithin_of_isOpen j hO hx] at hcomp
  exact hcomp.trans_eq (by rw [mul_pow]; ring)

/-- All normalized cutoffs obey `A_j*K^j` in the actual chart derivatives, with
one constant sequence chosen before the scale and the finite family. No factor
depending on the number of cutoffs occurs.

The hypotheses are the exact original provider obligations: actual pre-cutoff
derivatives bounded by `B_j*K^j`, actual square-sum derivatives bounded by
`C_j*K^j`, and the genuine pointwise lower bound on that same square sum.

Proof: obtain the preceding all-order composition bounds for the actual inverse
square root of the actual square sum. Native Leibniz gives the binomial sum of
the `i`-th pre-cutoff derivative and `(j-i)`-th reciprocal derivative. Each term
has scale `K^i*K^(j-i)=K^j`; sum only the fixed order-dependent constants.
Source: the full uniform-derivative conclusion of the square-normalization node.
-/
theorem exists_squareNormalizedCutoff_derivative_bounds
    (B C : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hC : ∀ j, 0 ≤ C j) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ (ι : Type*) [Fintype ι],
      ∀ (K : ℝ), 1 ≤ K → ∀ (b : ι → E → ℝ) (O : Set E), IsOpen O →
      (∀ i, ContDiffOn ℝ ∞ (b i) O) →
      (∀ x ∈ O, 1 ≤ squareCutoffSum b x) →
      (∀ j, ∀ x ∈ O, ‖iteratedFDeriv ℝ j (squareCutoffSum b) x‖ ≤ C j * K ^ j) →
      ∀ i, (∀ j, ∀ x ∈ O, ‖iteratedFDeriv ℝ j (b i) x‖ ≤ B j * K ^ j) →
      ∀ j, ∀ x ∈ O,
        ‖iteratedFDeriv ℝ j (squareNormalizedCutoff b i) x‖ ≤ A j * K ^ j := by
  obtain ⟨R, hR, hrecBound⟩ := exists_reciprocalSquareRoot_composition_bounds (E := E) C hC
  let A : ℕ → ℝ := fun j ↦
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * B l * R (j - l)
  refine ⟨A, fun j ↦ Finset.sum_nonneg
    (fun l _ ↦ mul_nonneg (mul_nonneg (by positivity) (hB l)) (hR (j - l))), ?_⟩
  intro ι _ K hK b O hO hb hSpos hSBound
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hS : ContDiffOn ℝ ∞ (squareCutoffSum b) O :=
    ContDiffOn.sum (fun i _ ↦ (hb i).pow 2)
  have hrec : ContDiffOn ℝ ∞ (reciprocalSquareRoot ∘ squareCutoffSum b) O :=
    reciprocalSquareRoot_contDiffOn.comp hS
      (fun x hx ↦ lt_of_lt_of_le zero_lt_one (hSpos x hx))
  have hrecBound' := hrecBound K hK (squareCutoffSum b) O hO hS hSpos hSBound
  intro i hbBound j x hx
  have hfull (l : ℕ) (a : E → ℝ) : iteratedFDerivWithin ℝ l a O x = iteratedFDeriv ℝ l a x :=
    iteratedFDerivWithin_of_isOpen l hO hx
  have hmul := norm_iteratedFDerivWithin_mul_le (hb i) hrec hO.uniqueDiffOn hx
    (n := j) (by simp)
  simp only [hfull] at hmul
  change ‖iteratedFDeriv ℝ j (fun y ↦ b i y * (reciprocalSquareRoot ∘ squareCutoffSum b) y) x‖ ≤ _
  apply hmul.trans
  calc
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (b i) x‖ *
        ‖iteratedFDeriv ℝ (j - l) (reciprocalSquareRoot ∘ squareCutoffSum b) x‖ ≤
      ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * (B l * K ^ l) *
        (R (j - l) * K ^ (j - l)) := by
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hbBound l x hx) (by positivity))
        (hrecBound' (j - l) x hx) (norm_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (hB l) (by positivity)))
    _ = A j * K ^ j := by
      dsimp only [A]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      have hlj : l ≤ j := by simpa using hl
      have hpowers : K ^ l * K ^ (j - l) = K ^ j := by
        rw [← pow_add, Nat.add_sub_of_le hlj]
      calc
        (j.choose l : ℝ) * (B l * K ^ l) * (R (j - l) * K ^ (j - l)) =
          ((j.choose l : ℝ) * B l * R (j - l)) * (K ^ l * K ^ (j - l)) := by ring
        _ = ((j.choose l : ℝ) * B l * R (j - l)) * K ^ j := by rw [hpowers]

end CoordinateBounds

section ManifoldNormalization

variable {ι E H M : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual square-normalized family is globally smooth on the original
manifold, provided its actual square sum is at least one.

Proof: finite sums and products make that SAME square sum smooth; compose it
with the actual real reciprocal square root away from zero and multiply by the
same original pre-cutoff. Source: the square-normalization node. -/
theorem squareNormalizedCutoff_contMDiff
    (b : ι → M → ℝ) (hb : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (b i))
    (hpos : ∀ x, 1 ≤ squareCutoffSum b x) (i : ι) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (squareNormalizedCutoff b i) := by
  have hS : ContMDiff I 𝓘(ℝ, ℝ) ∞ (squareCutoffSum b) := by
    unfold squareCutoffSum
    apply ContMDiff.sum
    intro j _
    exact (contDiff_id.pow 2).comp_contMDiff (hb j)
  have hrec : ContMDiff I 𝓘(ℝ, ℝ) ∞ (reciprocalSquareRoot ∘ squareCutoffSum b) := by
    intro x
    have hp : ContDiffAt ℝ ∞ reciprocalSquareRoot (squareCutoffSum b x) :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt (lt_of_lt_of_le zero_lt_one (hpos x)))
    exact hp.comp_contMDiffAt (hS x)
  exact (hb i).mul hrec

/-- Compact support of each actual pre-cutoff is retained by normalization.
Proof: use the native compact-support multiplication lemma.
Source: the support conclusion of the square-normalization node. -/
theorem squareNormalizedCutoff_hasCompactSupport
    (b : ι → M → ℝ) (i : ι) (hb : HasCompactSupport (b i)) :
    HasCompactSupport (squareNormalizedCutoff b i) := hb.mul_right

end ManifoldNormalization

section ActualChartEndpoint

variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The full actual square-normalization conclusion with the original chart
interface: each cutoff needs only its OWN centered-chart derivative bounds,
together with the square-sum bounds in that same chart. One sequence `A_j` is
chosen before the scale, manifold functions, or chart family.

The output is the literal normalized family, globally smooth, with exact sum of
squares one and both ordinary and topological supports retained. Every actual
order-`j` derivative of its OWN chart representative is bounded by `A_j*K^j`.
No bound on the other individual cutoffs in that chart is assumed; their
aggregate enters only through the original actual square-sum provider.

Proof: apply the preceding native all-order product/composition estimate in
each given genuine chart. The actual pullback of the finite square sum is
definitionally the finite square sum of the actual pullbacks. Smoothness of each
chart pullback follows from the original map smoothness and the actual smooth
inverse chart. Source: the complete original square-normalization node, given
its stated scaled-bump and bounded-square-sum provider bounds.
-/
theorem exists_uniform_squareNormalizedCutoffs
    (B C : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hC : ∀ j, 0 ≤ C j) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ (ι : Type*) [Fintype ι],
      ∀ (K : ℝ), 1 ≤ K → ∀ (b : ι → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b i)) →
      (∀ x, 1 ≤ squareCutoffSum b x) →
      ∀ e : ι → OpenPartialHomeomorph M E,
      (∀ i, e i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) →
      (∀ i j, ∀ y ∈ (e i).target,
        ‖iteratedFDeriv ℝ j (b i ∘ (e i).symm) y‖ ≤ B j * K ^ j) →
      (∀ i j, ∀ y ∈ (e i).target,
        ‖iteratedFDeriv ℝ j (squareCutoffSum b ∘ (e i).symm) y‖ ≤ C j * K ^ j) →
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (squareNormalizedCutoff b i)) ∧
      (∀ x, ∑ i, squareNormalizedCutoff b i x ^ 2 = 1) ∧
      (∀ i, Function.support (squareNormalizedCutoff b i) ⊆ Function.support (b i)) ∧
      (∀ i, tsupport (squareNormalizedCutoff b i) ⊆ tsupport (b i)) ∧
      ∀ i j, ∀ y ∈ (e i).target,
        ‖iteratedFDeriv ℝ j (squareNormalizedCutoff b i ∘ (e i).symm) y‖ ≤ A j * K ^ j := by
  obtain ⟨A, hA, hbound⟩ := exists_squareNormalizedCutoff_derivative_bounds
    (E := E) B C hB hC
  refine ⟨A, hA, ?_⟩
  intro ι _ K hK b hb hpos e he hbBound hSBound
  refine ⟨squareNormalizedCutoff_contMDiff b hb hpos,
    fun x ↦ squareNormalizedCutoff_sum_sq b x (lt_of_lt_of_le zero_lt_one (hpos x)),
    squareNormalizedCutoff_support_subset b,
    squareNormalizedCutoff_tsupport_subset b, ?_⟩
  intro i j y hy
  have hcoord (l : ι) : ContDiffOn ℝ ∞ (b l ∘ (e i).symm) (e i).target :=
    ((hb l).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (he i))).contDiffOn
  exact hbound ι K hK (fun l ↦ b l ∘ (e i).symm) (e i).target (e i).open_target
    hcoord (fun z _ ↦ hpos ((e i).symm z)) (hSBound i) i (hbBound i) j y hy

end ActualChartEndpoint

#print axioms reciprocalSquareRoot_contDiffOn
#print axioms one_le_squareCutoffSum_of_plateau
#print axioms squareNormalizedCutoff_sum_sq
#print axioms squareNormalizedCutoff_support_subset
#print axioms squareNormalizedCutoff_tsupport_subset
#print axioms exists_reciprocalSquareRoot_derivative_bounds
#print axioms exists_reciprocalSquareRoot_composition_bounds
#print axioms exists_squareNormalizedCutoff_derivative_bounds
#print axioms squareNormalizedCutoff_contMDiff
#print axioms squareNormalizedCutoff_hasCompactSupport
#print axioms exists_uniform_squareNormalizedCutoffs

end GlobalEmbedding.Offline
