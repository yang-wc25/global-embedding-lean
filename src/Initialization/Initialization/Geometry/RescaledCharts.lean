import Initialization.Geometry.TranslatedCharts
import Mathlib.Geometry.Manifold.Algebra.SMul

/-! Actual centered and rescaled maximal-atlas charts. -/

open Set Metric Manifold IsManifold
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

/-- The actual chart y = T (e(x) - p), with its exact inverse and domain. -/
def rescaledChart (e : OpenPartialHomeomorph M E) (p : E) (T : ℝ) (hT : T ≠ 0) :
    OpenPartialHomeomorph M E where
  toFun x := T • (e x - p)
  invFun y := e.symm (T⁻¹ • y + p)
  source := e.source
  target := {y | T⁻¹ • y + p ∈ e.target}
  map_source' := by intro x hx; simpa [smul_smul, hT] using e.map_source hx
  map_target' := by intro y hy; exact e.map_target hy
  left_inv' := by intro x hx; simpa [smul_smul, hT] using e.left_inv hx
  right_inv' := by
    intro y hy
    change T • (e (e.symm (T⁻¹ • y + p)) - p) = y
    rw [e.right_inv hy]
    simp [smul_smul, hT]
  open_source := e.open_source
  open_target := e.open_target.preimage ((continuous_const.smul continuous_id).add continuous_const)
  continuousOn_toFun := continuousOn_const.smul (e.continuousOn.sub continuousOn_const)
  continuousOn_invFun := e.continuousOn_symm.comp
    ((continuousOn_const.smul continuousOn_id).add continuousOn_const) (fun _ hy ↦ hy)

@[simp] theorem rescaledChart_apply (e : OpenPartialHomeomorph M E) (p : E)
    (T : ℝ) (hT : T ≠ 0) (x : M) :
    rescaledChart e p T hT x = T • (e x - p) := rfl

@[simp] theorem rescaledChart_symm_apply (e : OpenPartialHomeomorph M E) (p : E)
    (T : ℝ) (hT : T ≠ 0) (y : E) :
    (rescaledChart e p T hT).symm y = e.symm (T⁻¹ • y + p) := rfl

@[simp] theorem rescaledChart_source (e : OpenPartialHomeomorph M E) (p : E)
    (T : ℝ) (hT : T ≠ 0) : (rescaledChart e p T hT).source = e.source := rfl

@[simp] theorem rescaledChart_target (e : OpenPartialHomeomorph M E) (p : E)
    (T : ℝ) (hT : T ≠ 0) :
    (rescaledChart e p T hT).target = {y | T⁻¹ • y + p ∈ e.target} := rfl

/-- Membership is proved in the original smooth maximal atlas. -/
theorem rescaledChart_mem_maximalAtlas [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (p : E)
    (T : ℝ) (hT : T ≠ 0) :
    rescaledChart e p T hT ∈ maximalAtlas 𝓘(ℝ, E) ∞ M := by
  have hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : E ↦ T • y) :=
    (contDiff_const.smul contDiff_id).contMDiff
  have hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y : E ↦ T⁻¹ • y + p) :=
    ((contDiff_const.smul contDiff_id).add contDiff_const).contMDiff
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact hs.comp_contMDiffOn ((contMDiffOn_of_mem_maximalAtlas he).sub contMDiffOn_const)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      hi.contMDiffOn (fun _ hy ↦ hy)

/-- A positive coordinate buffer is independent of the center and every T≥1. -/
theorem rescaledChart_closedBall_buffer
    (e : OpenPartialHomeomorph M E) {a p : E} {r ρ T : ℝ}
    (hr : 0 < r) (hρ : ρ ≤ r) (hp : p ∈ closedBall a r)
    (hbuffer : closedBall a (4 * r) ⊆ e.target) (hT : 1 ≤ T) :
    closedBall (0 : E) ρ ⊆
      (rescaledChart e p T (ne_of_gt (zero_lt_one.trans_le hT))).target := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  intro y hy
  change T⁻¹ • y + p ∈ e.target
  apply translatedChart_closedBall_buffer e hr hρ hp hbuffer
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖T⁻¹ • y‖ = T⁻¹ * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hTpos)]
    _ ≤ ‖y‖ := mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hT)
    _ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hy

/-- Exact coordinate-size conversion, with a real positive scale. -/
theorem norm_rescaledChart
    (e : OpenPartialHomeomorph M E) (p : E) {T : ℝ} (hT : 0 < T) (x : M) :
    ‖rescaledChart e p T hT.ne' x‖ = T * dist (e x) p := by
  simp only [rescaledChart_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos hT, dist_eq_norm]

end GlobalEmbedding.Initialization
