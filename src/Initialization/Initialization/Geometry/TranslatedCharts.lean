import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic

/-! Genuine centered charts obtained by translating a fixed smooth chart.
These replace geodesic coordinates only in the alternate proof route; they are
actual maximal-atlas members, not independently supplied coordinate functions. -/

open Set Metric Manifold IsManifold
open scoped ContDiff Manifold

namespace GlobalEmbedding.Initialization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

/-- Subtract a coordinate center from an actual chart. The inverse adds the
same center before applying the original inverse, and the source is unchanged. -/
def translatedChart (e : OpenPartialHomeomorph M E) (p : E) :
    OpenPartialHomeomorph M E where
  toFun x := e x - p
  invFun y := e.symm (y + p)
  source := e.source
  target := {y | y + p ∈ e.target}
  map_source' := by intro x hx; simpa using e.map_source hx
  map_target' := by intro y hy; exact e.map_target hy
  left_inv' := by intro x hx; simpa using e.left_inv hx
  right_inv' := by intro y hy; simpa using congrArg (fun z ↦ z - p) (e.right_inv hy)
  open_source := e.open_source
  open_target := e.open_target.preimage (continuous_id.add continuous_const)
  continuousOn_toFun := e.continuousOn.sub continuousOn_const
  continuousOn_invFun := e.continuousOn_symm.comp
    (continuousOn_id.add continuousOn_const) (fun _ hy ↦ hy)

@[simp] theorem translatedChart_apply (e : OpenPartialHomeomorph M E) (p : E) (x : M) :
    translatedChart e p x = e x - p := rfl

@[simp] theorem translatedChart_symm_apply (e : OpenPartialHomeomorph M E) (p y : E) :
    (translatedChart e p).symm y = e.symm (y + p) := rfl

@[simp] theorem translatedChart_source (e : OpenPartialHomeomorph M E) (p : E) :
    (translatedChart e p).source = e.source := rfl

@[simp] theorem translatedChart_target (e : OpenPartialHomeomorph M E) (p : E) :
    (translatedChart e p).target = {y | y + p ∈ e.target} := rfl

/-- Translating the values of an actual smooth chart preserves membership in
exactly the original maximal smooth atlas. -/
theorem translatedChart_mem_maximalAtlas [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (p : E) :
    translatedChart e p ∈ maximalAtlas 𝓘(ℝ, E) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas he).sub contMDiffOn_const
  · exact (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      ((contMDiff_id.add contMDiff_const).contMDiffOn) (fun _ hy ↦ hy)

/-- A fixed four-radius chart buffer works at every center in its compact
one-radius core. The common radius can be decreased before choosing K,T. -/
theorem translatedChart_closedBall_buffer
    (e : OpenPartialHomeomorph M E) {a p : E} {r ρ : ℝ}
    (hr : 0 < r) (hρ : ρ ≤ r) (hp : p ∈ closedBall a r)
    (hbuffer : closedBall a (4 * r) ⊆ e.target) :
    closedBall (0 : E) ρ ⊆ (translatedChart e p).target := by
  intro y hy
  apply hbuffer
  rw [Metric.mem_closedBall]
  have h1 : ‖y‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have h2 : dist p a ≤ r := hp
  have h3 : dist (y + p) p = ‖y‖ := by simp [dist_eq_norm]
  have h4 := dist_triangle (y + p) p a
  linarith

end GlobalEmbedding.Initialization
