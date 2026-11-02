import Initialization.Colored.SmoothMap

/-!
# Local multiplicity of the actual color coordinates

The finite same-color disjointness condition gives an equality on one actual
neighborhood, not just at its center. Thus every derivative of a color sum is
that of at most one cutoff-weighted exponential, independently of the total
number of patches. No limiting argument or chart-count constant is introduced.
-/

noncomputable section

open Function Set Metric Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- Outside a cutoff's topological support, its actual phase term vanishes on
an open neighborhood, regardless of the behavior of the unsupported phase. -/
theorem coloredWave_eventually_zero (χ ℓ : X → ℝ) (T : ℝ) (x : X)
    (hx : x ∉ tsupport χ) : coloredWave χ ℓ T =ᶠ[𝓝 x] 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  simp only [coloredWave, hy, zero_smul, Pi.zero_apply]

/-- At a point in one cutoff support, the same color coordinate is the one
actual supported term on a whole neighborhood. Boundary points are included. -/
theorem coloredCoordinate_eventually_single {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (x : X) (i : ι) (hxi : x ∈ tsupport (χ i)) :
    coloredCoordinate color χ ℓ T (color i) =ᶠ[𝓝 x] coloredWave (χ i) (ℓ i) T := by
  classical
  have ht : ∀ j, ∀ᶠ y in 𝓝 x,
      (if color j = color i then coloredWave (χ j) (ℓ j) T y else 0) =
        if j = i then coloredWave (χ i) (ℓ i) T y else 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall (fun _ ↦ by simp)
    · by_cases hc : color j = color i
      · have hxj : x ∉ tsupport (χ j) := by
          intro hxj
          exact Set.disjoint_left.mp (hdisjoint j i hji hc) hxj hxi
        filter_upwards [coloredWave_eventually_zero (χ j) (ℓ j) T x hxj] with y hy
        simp only [hc, hji, ite_true, ite_false, hy, Pi.zero_apply]
      · exact Filter.Eventually.of_forall (fun _ ↦ by simp [hc, hji])
  filter_upwards [Filter.eventually_all.mpr ht] with y hy
  dsimp only [coloredCoordinate]
  calc
    _ = ∑ j, if j = i then coloredWave (χ i) (ℓ i) T y else 0 :=
      Finset.sum_congr rfl (fun j _ ↦ hy j)
    _ = _ := by simp

/-- If no same-color topological support meets the center, that entire actual
color coordinate vanishes on a common neighborhood. Finiteness gives the common
neighborhood; no global zero extension regularity is assumed. -/
theorem coloredCoordinate_eventually_zero {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → X → ℝ) (T : ℝ) (c : Fin C) (x : X)
    (hx : ∀ i, color i = c → x ∉ tsupport (χ i)) :
    coloredCoordinate color χ ℓ T c =ᶠ[𝓝 x] 0 := by
  classical
  have ht : ∀ i, ∀ᶠ y in 𝓝 x,
      (if color i = c then coloredWave (χ i) (ℓ i) T y else 0) = 0 := by
    intro i
    by_cases hc : color i = c
    · filter_upwards [coloredWave_eventually_zero (χ i) (ℓ i) T x (hx i hc)] with y hy
      simpa only [hc, ite_true, Pi.zero_apply] using hy
    · exact Filter.Eventually.of_forall (fun _ ↦ by simp [hc])
  filter_upwards [Filter.eventually_all.mpr ht] with y hy
  exact Finset.sum_eq_zero (fun i _ ↦ hy i)

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Each arbitrary-order jet is exactly zero or exactly the jet of one actual
local term. No cardinality of the patch index type occurs. -/
theorem coloredCoordinate_jet_single_or_zero {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (c : Fin C) (x : E) (j : ℕ) :
    (∃ i, color i = c ∧ x ∈ tsupport (χ i) ∧
      iteratedFDeriv ℝ j (coloredCoordinate color χ ℓ T c) x =
        iteratedFDeriv ℝ j (coloredWave (χ i) (ℓ i) T) x) ∨
      iteratedFDeriv ℝ j (coloredCoordinate color χ ℓ T c) x = 0 := by
  classical
  by_cases hactive : ∃ i, color i = c ∧ x ∈ tsupport (χ i)
  · obtain ⟨i, hic, hxi⟩ := hactive
    left
    refine ⟨i, hic, hxi, ?_⟩
    subst c
    exact ((coloredCoordinate_eventually_single color χ ℓ hdisjoint T x i hxi).iteratedFDeriv ℝ j).self_of_nhds
  · right
    have hx : ∀ i, color i = c → x ∉ tsupport (χ i) := by
      intro i hic hxi
      exact hactive ⟨i, hic, hxi⟩
    have hjet := ((coloredCoordinate_eventually_zero color χ ℓ T c x hx).iteratedFDeriv ℝ j).self_of_nhds
    rw [hjet]
    cases j with
    | zero => ext v; simp
    | succ j => exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := E)
        (Nat.succ_ne_zero j) (0 : ℂ)) x

/-- The actual color coordinate inherits a uniform jet bound from its active
terms with constant one, not the size of the finite cutoff family. -/
theorem coloredCoordinate_jet_bound {C : ℕ} (color : ι → Fin C)
    (χ ℓ : ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (T : ℝ) (c : Fin C) (x : E) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hterms : ∀ i, x ∈ tsupport (χ i) →
      ‖iteratedFDeriv ℝ j (coloredWave (χ i) (ℓ i) T) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ j (coloredCoordinate color χ ℓ T c) x‖ ≤ A := by
  rcases coloredCoordinate_jet_single_or_zero color χ ℓ hdisjoint T c x j with
    ⟨i, _, hxi, heq⟩ | hzero
  · rw [heq]
    exact hterms i hxi
  · simpa only [hzero, norm_zero] using hA

end Derivatives

end GlobalEmbedding.Initialization
