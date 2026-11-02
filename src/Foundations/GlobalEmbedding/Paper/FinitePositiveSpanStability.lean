import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Order.Lattice

/-!
# Robust actual finite positive spanning

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines327–332.
DAG node: `finite-positive-span-stability`.
-/
noncomputable section
open Set Metric
open scoped RealInnerProductSpace
namespace GlobalEmbedding.Paper

/-- Strictly positive support in every actual nonzero direction has a uniform
positive margin on the compact genuine Euclidean unit sphere. -/
theorem finite_positive_support_margin
    {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (v : ι → E) (hpos : ∀ ξ : E, ξ ≠ 0 → ∃ i, 0 < ⟪ξ, v i⟫) :
    ∃ r : ℝ, 0 < r ∧ ∀ ξ : E, ‖ξ‖ = 1 → ∃ i, r ≤ ⟪ξ, v i⟫ := by
  classical
  let m : E → ℝ := fun ξ ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ⟪ξ, v i⟫)
  have hm : Continuous m := Continuous.finset_sup'_apply _
    (fun _ _ ↦ continuous_id.inner continuous_const)
  have hmp : ∀ ξ ∈ sphere (0 : E) 1, 0 < m ξ := by
    intro ξ hξ
    have hn : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
    have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hn
    obtain ⟨i, hi⟩ := hpos ξ hξ0
    exact hi.trans_le (Finset.le_sup' (fun i ↦ ⟪ξ, v i⟫) (Finset.mem_univ i))
  by_cases hs : (sphere (0 : E) 1).Nonempty
  · obtain ⟨ξ₀, hξ₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hm.continuousOn
    refine ⟨m ξ₀, hmp ξ₀ hξ₀, ?_⟩
    intro ξ hξ
    have hh := hmin (mem_sphere_zero_iff_norm.mpr hξ)
    exact (Finset.le_sup'_iff _).mp hh |>.imp (fun i hi ↦ hi.2)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ξ hξ
    exact (hs ⟨ξ, mem_sphere_zero_iff_norm.mpr hξ⟩).elim

/-- A uniform actual support margin forces the actual finite convex hull to contain
the closed Euclidean ball. The proof uses true strict separation and Riesz duality. -/
theorem closedBall_subset_convexHull_of_finite_support
    {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (v : ι → E) (r : ℝ)
    (hmargin : ∀ ξ : E, ‖ξ‖ = 1 → ∃ i, r ≤ ⟪ξ, v i⟫) :
    closedBall (0 : E) r ⊆ convexHull ℝ (range v) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro x hx
  by_contra houtside
  obtain ⟨ℓ, c, hvc, hcx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range v)) ((finite_range v).isClosed_convexHull ℝ) houtside
  let ξ : E := (InnerProductSpace.toDual ℝ E).symm ℓ
  have hrepr (y : E) : ⟪ξ, y⟫ = ℓ y := InnerProductSpace.toDual_symm_apply
  have hξ : ξ ≠ 0 := by
    intro hzero
    have hℓ (y : E) : ℓ y = 0 := by rw [← hrepr, hzero, inner_zero_left]
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := hvc (v i) (subset_convexHull ℝ (range v) (mem_range_self i))
    rw [hℓ] at hi hcx
    linarith
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hunit : ‖(‖ξ‖⁻¹ : ℝ) • ξ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨i, hi⟩ := hmargin ((‖ξ‖⁻¹ : ℝ) • ξ) hunit
  rw [real_inner_smul_left] at hi
  have hvi : r * ‖ξ‖ ≤ ⟪ξ, v i⟫ := by
    have hh := mul_le_mul_of_nonneg_left hi hn.le
    field_simp at hh
    nlinarith
  have hstrict := hvc (v i) (subset_convexHull ℝ (range v) (mem_range_self i))
  have hxn : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
  have hinner : ⟪ξ, x⟫ ≤ ‖ξ‖ * r :=
    (real_inner_le_norm ξ x).trans (mul_le_mul_of_nonneg_left hxn hn.le)
  rw [hrepr] at hvi hinner
  nlinarith

/-- Norm perturbations smaller than half the actual support margin preserve a
closed ball and a common positive support margin, for arbitrary finite actual families. -/
theorem finite_positive_span_stable
    {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (v : ι → E) (hpos : ∀ ξ : E, ξ ≠ 0 → ∃ i, 0 < ⟪ξ, v i⟫) :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ ∀ w : ι → E,
      (∀ i, ‖w i - v i‖ ≤ ε) →
      (∀ ξ : E, ‖ξ‖ = 1 → ∃ i, r ≤ ⟪ξ, w i⟫) ∧
      closedBall (0 : E) r ⊆ convexHull ℝ (range w) := by
  obtain ⟨δ, hδ, hmargin⟩ := finite_positive_support_margin v hpos
  refine ⟨δ / 2, δ / 2, half_pos hδ, half_pos hδ, ?_⟩
  intro w hw
  have hs : ∀ ξ : E, ‖ξ‖ = 1 → ∃ i, δ / 2 ≤ ⟪ξ, w i⟫ := by
    intro ξ hξ
    obtain ⟨i, hi⟩ := hmargin ξ hξ
    refine ⟨i, ?_⟩
    have hh := real_inner_le_norm ξ (v i - w i)
    rw [inner_sub_right, hξ, one_mul, norm_sub_rev] at hh
    have hd := hw i
    linarith
  exact ⟨hs, closedBall_subset_convexHull_of_finite_support w (δ / 2) hs⟩

end GlobalEmbedding.Paper
