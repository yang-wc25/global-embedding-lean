import GlobalEmbedding.Paper.FreeHopfProductNative
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The actual colored phase map in equation (7.2)

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 805--813.
The functions are the literal finite colored sums of cutoff-weighted period-one
complex exponentials. Same-color disjointness and the square partition imply
membership in the actual native complex unit sphere. The cutoff and phase
providers are explicit intermediate inputs, not additional hypotheses of the
full initialization target.
-/

noncomputable section

open Function Set Metric Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization

open GlobalEmbedding.Paper

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- One literal term of (7.2), using a real frequency, not an integral one. -/
def coloredWave (χ ℓ : X → ℝ) (T : ℝ) (x : X) : ℂ :=
  χ x • (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ)

/-- A color coordinate of (7.2), before restricting to the genuine sphere. -/
def coloredCoordinate {C : ℕ} (color : ι → Fin C) (χ ℓ : ι → X → ℝ)
    (T : ℝ) (c : Fin C) (x : X) : ℂ :=
  ∑ i, if color i = c then coloredWave (χ i) (ℓ i) T x else 0

/-- The actual complex Euclidean ambient map, with its native L² norm. -/
def coloredAmbient {C : ℕ} (color : ι → Fin C) (χ ℓ : ι → X → ℝ)
    (T : ℝ) (x : X) : PlanarHopfAmbient C :=
  WithLp.toLp 2 (fun c ↦ coloredCoordinate color χ ℓ T c x)

@[simp] theorem coloredWave_norm_sq (χ ℓ : X → ℝ) (T : ℝ) (x : X) :
    ‖coloredWave χ ℓ T x‖ ^ 2 = χ x ^ 2 := by
  simp only [coloredWave, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, sq_abs]

/-- Only one active index may have a specified color, pointwise on any source,
including disconnected sources. This follows from actual topological supports. -/
theorem colored_active_unique {C : ℕ} (color : ι → Fin C) (χ : ι → X → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (x : X) {i j : ι} (hi : χ i x ≠ 0) (hj : χ j x ≠ 0)
    (hcolor : color i = color j) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (hdisjoint i j hij hcolor)
    (subset_tsupport (χ i) hi) (subset_tsupport (χ j) hj)

/-- Same-color disjointness removes every cross term of the actual finite sum.
No orthogonality or formal Gram data is imposed on the desired map. -/
theorem coloredCoordinate_norm_sq {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (c : Fin C) (x : X) :
    ‖coloredCoordinate color χ ℓ T c x‖ ^ 2 =
      ∑ i, if color i = c then χ i x ^ 2 else 0 := by
  classical
  by_cases hactive : ∃ i, color i = c ∧ χ i x ≠ 0
  · obtain ⟨i, hic, hi⟩ := hactive
    have hzero (j : ι) (hji : j ≠ i) (hjc : color j = c) : χ j x = 0 := by
      by_contra hj
      exact hji (colored_active_unique color χ hdisjoint x hj hi (hjc.trans hic.symm))
    have hsum : coloredCoordinate color χ ℓ T c x = coloredWave (χ i) (ℓ i) T x := by
      dsimp only [coloredCoordinate]
      rw [Finset.sum_eq_single i]
      · simp [hic]
      · intro j _ hji
        by_cases hjc : color j = c
        · simp [hjc, coloredWave, hzero j hji hjc]
        · simp [hjc]
      · simp
    rw [hsum, coloredWave_norm_sq, Finset.sum_eq_single i]
    · simp [hic]
    · intro j _ hji
      by_cases hjc : color j = c
      · simp [hjc, hzero j hji hjc]
      · simp [hjc]
    · simp
  · have hz (i : ι) (hic : color i = c) : χ i x = 0 := by
      by_contra hi
      exact hactive ⟨i, hic, hi⟩
    have hsum : coloredCoordinate color χ ℓ T c x = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hic : color i = c
      · simp [hic, coloredWave, hz i hic]
      · simp [hic]
    rw [hsum]
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases hic : color i = c
    · simp [hic, hz i hic]
    · simp [hic]

/-- The actual ambient map has norm one. This is the exact square-partition
identity in the paper; it is not an assumed sphere-valued field. -/
theorem coloredAmbient_mem_sphere {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ) (x : X) :
    coloredAmbient color χ ℓ T x ∈ sphere (0 : PlanarHopfAmbient C) 1 := by
  apply mem_sphere_zero_iff_norm.mpr
  have hnorm : ‖coloredAmbient color χ ℓ T x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ c, ‖coloredCoordinate color χ ℓ T c x‖ ^ 2) = 1
    simp_rw [coloredCoordinate_norm_sq color χ ℓ hdisjoint T]
    rw [Finset.sum_comm]
    simpa using hsquare x
  nlinarith [norm_nonneg (coloredAmbient color χ ℓ T x)]

/-- The genuinely sphere-valued factor of (7.2). -/
def coloredSphere {C : ℕ} (color : ι → Fin C) (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ) (x : X) :
    PlanarHopfSphere C :=
  ⟨coloredAmbient color χ ℓ T x,
    coloredAmbient_mem_sphere color χ ℓ hdisjoint hsquare T x⟩

end GlobalEmbedding.Initialization
