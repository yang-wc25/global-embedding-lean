import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-!
# Actual parameter-local phase sampling and persistence

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines327–332.
DAG node: `cone-parameter-phase-sampling`.
-/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace GlobalEmbedding.Paper

/-- Exact high-frequency phase samples persist on a genuine open parameter
neighborhood of an actual regular base point. The family is only required to be
jointly continuous; its genuine strict derivative is used at the base point alone. -/
theorem matrix_parametric_phase_sampling
    {P : Type*} [TopologicalSpace P] (q : P → ℝ → ℝ)
    (hq : Continuous (fun p : P × ℝ ↦ q p.1 p.2))
    (p₀ : P) (a q' : ℝ) (hd : HasStrictDerivAt (q p₀) q' a) (hq' : q' ≠ 0)
    (U : Set ℝ) (hU : U ∈ 𝓝 a) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧ ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ p ∈ W, ∀ T : ℝ, T₀ ≤ T → ∀ φ : ℝ, ∃ t ∈ U, ∃ n : ℤ,
        T * q p t = φ + 2 * Real.pi * n := by
  obtain ⟨η, hη, htime⟩ := Metric.mem_nhds_iff.mp hU
  have himage : q p₀ '' ball a η ∈ 𝓝 (q p₀ a) := by
    rw [← hd.map_nhds_eq hq']
    change (q p₀) ⁻¹' (q p₀ '' ball a η) ∈ 𝓝 a
    exact mem_of_superset (ball_mem_nhds a hη) (fun t ht ↦ ⟨t, ht, rfl⟩)
  obtain ⟨δ, hδ, hvalue⟩ := Metric.mem_nhds_iff.mp himage
  have hlo : q p₀ a - δ / 2 ∈ ball (q p₀ a) δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hhi : q p₀ a + δ / 2 ∈ ball (q p₀ a) δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  obtain ⟨tlo, htlo, hqlo⟩ := hvalue hlo
  obtain ⟨thi, hthi, hqhi⟩ := hvalue hhi
  let W : Set P := {p | δ / 2 < q p thi - q p tlo}
  have hgap : Continuous (fun p : P ↦ q p thi - q p tlo) :=
    (hq.comp (continuous_id.prodMk continuous_const)).sub
      (hq.comp (continuous_id.prodMk continuous_const))
  have hW : IsOpen W := hgap.isOpen_preimage _ isOpen_Ioi
  have hp₀ : p₀ ∈ W := by
    change δ / 2 < q p₀ thi - q p₀ tlo
    rw [hqhi, hqlo]
    linarith
  refine ⟨W, hW, hp₀, 4 * Real.pi / δ + 1, by positivity, ?_⟩
  intro p hp T hT₀ φ
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hT₀
  have hsmall : 2 * Real.pi / T < δ / 2 := by
    have hh : 4 * Real.pi / δ < T := by linarith
    have hh' := (div_lt_iff₀ hδ).mp hh
    apply (div_lt_iff₀ hT).mpr
    nlinarith
  have hgap' : δ / 2 < q p thi - q p tlo := hp
  let n : ℤ := ⌈(T * q p tlo - φ) / (2 * Real.pi)⌉
  have hpi : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hnlo := Int.le_ceil ((T * q p tlo - φ) / (2 * Real.pi))
  have hnhi := Int.ceil_lt_add_one ((T * q p tlo - φ) / (2 * Real.pi))
  change _ ≤ (n : ℝ) at hnlo
  change (n : ℝ) < _ at hnhi
  let y : ℝ := (φ + 2 * Real.pi * n) / T
  have hylo : q p tlo ≤ y := by
    apply (le_div_iff₀ hT).mpr
    have hh := (div_le_iff₀ hpi).mp hnlo
    nlinarith
  have hyhi : y < q p thi := by
    apply (div_lt_iff₀ hT).mpr
    have hnhi' : (n : ℝ) - 1 < (T * q p tlo - φ) / (2 * Real.pi) := by
      linarith
    have hh := (lt_div_iff₀ hpi).mp hnhi'
    have hspan : 2 * Real.pi < T * (q p thi - q p tlo) := by
      have hs := (div_lt_iff₀ hT).mp hsmall
      nlinarith
    nlinarith
  have hcont : ContinuousOn (q p) (uIcc tlo thi) :=
    (hq.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hyv : y ∈ uIcc (q p tlo) (q p thi) :=
    Icc_subset_uIcc ⟨hylo, hyhi.le⟩
  obtain ⟨t, ht, hqt⟩ := intermediate_value_uIcc hcont hyv
  have htu : t ∈ U := htime ((convex_ball a η).ordConnected.uIcc_subset htlo hthi ht)
  refine ⟨t, htu, n, ?_⟩
  rw [hqt]
  exact mul_div_cancel₀ _ hT.ne'

end GlobalEmbedding.Paper
