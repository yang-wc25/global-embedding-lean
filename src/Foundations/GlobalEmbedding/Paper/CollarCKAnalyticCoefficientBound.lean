import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Actual geometric finite-coordinate coefficient bounds from analyticity

Source: Gantumur, Math580 notes2, Theorem18 coefficient majorant construction.
DAG: `collar-ck-analytic-coefficient-bound`. Exclusive owner W4.
No formal PDE, Taylor coefficient convention or solution carrier is defined here.
-/
noncomputable section
open scoped BigOperators

namespace GlobalEmbedding.Paper

variable {E F Idx : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype Idx]

/-- Every finite-coordinate coefficient sum of a genuinely convergent multilinear series
has one geometric bound. The number of coordinate words is absorbed in a smaller radius.
The coefficient is written as its actual finite sum, so this applies to every monomial fiber
without introducing another Taylor coefficient definition. Empty alphabets and degree zero
are included by the positive factor max(1, card Idx). -/
theorem collarCKFiniteCoordinateGeometricBound
    (p : FormalMultilinearSeries ℝ E F) (hp : 0 < p.radius)
    (e : Idx → E) (he : ∀ i, ‖e i‖ ≤ 1) :
    ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
      ∀ k (S : Finset (Fin k → Idx)),
        ‖∑ w ∈ S, p k (fun i ↦ e (w i))‖ ≤ M / R ^ k := by
  classical
  obtain ⟨r, hr, hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hrpos : 0 < r := by exact_mod_cast hr
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hrpos
  obtain ⟨M, hM, hbound⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hrpos hrp
  let D : ℝ := max 1 (Fintype.card Idx : ℝ)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨M, (r : ℝ) / D, hM, div_pos hrreal hD, ?_⟩
  intro k S
  have hword (w : Fin k → Idx) : ‖p k (fun i ↦ e (w i))‖ ≤ M / (r : ℝ) ^ k := by
    have hv : ‖p k (fun i ↦ e (w i))‖ ≤ ‖p k‖ := by
      simpa only [Finset.prod_const_one, mul_one] using
        (p k).le_opNorm_mul_prod_of_le (b := fun _ ↦ (1 : ℝ)) (fun i ↦ he (w i))
    exact hv.trans (hbound k)
  have hcard : (S.card : ℝ) ≤ D ^ k := by
    calc
      (S.card : ℝ) ≤ (Fintype.card (Fin k → Idx) : ℝ) := by
        exact_mod_cast S.card_le_univ
      _ = (Fintype.card Idx : ℝ) ^ k := by simp
      _ ≤ D ^ k := by
        dsimp only [D]
        gcongr
        exact le_max_right _ _
  calc
    ‖∑ w ∈ S, p k (fun i ↦ e (w i))‖ ≤ ∑ w ∈ S, ‖p k (fun i ↦ e (w i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w ∈ S, M / (r : ℝ) ^ k := Finset.sum_le_sum fun w _ ↦ hword w
    _ = (S.card : ℝ) * (M / (r : ℝ) ^ k) := by simp
    _ ≤ D ^ k * (M / (r : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = M / ((r : ℝ) / D) ^ k := by
      rw [div_pow]
      field_simp

/-- Analyticity of the actual RHS supplies both its genuine multilinear expansion and actual
positive geometric constants. No coefficient bound is an input to this theorem. -/
theorem collarCKAnalyticFiniteCoordinateBound
    (f : E → F) (x : E) (hf : AnalyticAt ℝ f x)
    (e : Idx → E) (he : ∀ i, ‖e i‖ ≤ 1) :
    ∃ p : FormalMultilinearSeries ℝ E F, HasFPowerSeriesAt f p x ∧
      ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
        ∀ k (S : Finset (Fin k → Idx)),
          ‖∑ w ∈ S, p k (fun i ↦ e (w i))‖ ≤ M / R ^ k := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp, collarCKFiniteCoordinateGeometricBound p hp.radius_pos e he⟩

/-- For the actual normalized RHS, the same genuine expansion additionally has zero constant
coefficient. This is the precise reason that the rational geometric majorant may subtract 1. -/
theorem collarCKNormalizedAnalyticFiniteCoordinateBound
    (f : E → F) (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 0)
    (e : Idx → E) (he : ∀ i, ‖e i‖ ≤ 1) :
    ∃ p : FormalMultilinearSeries ℝ E F, HasFPowerSeriesAt f p 0 ∧
      (∀ v : Fin 0 → E, p 0 v = 0) ∧
      ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
        ∀ k (S : Finset (Fin k → Idx)),
          ‖∑ w ∈ S, p k (fun i ↦ e (w i))‖ ≤ M / R ^ k := by
  obtain ⟨p, hp, hbound⟩ := collarCKAnalyticFiniteCoordinateBound f 0 hf e he
  exact ⟨p, hp, fun v ↦ (hp.coeff_zero v).trans hf0, hbound⟩

#print axioms collarCKNormalizedAnalyticFiniteCoordinateBound
#print axioms collarCKFiniteCoordinateGeometricBound
#print axioms collarCKAnalyticFiniteCoordinateBound

end GlobalEmbedding.Paper
