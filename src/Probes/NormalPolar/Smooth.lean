import NormalPolar.InverseSqrtSeries
import Probes.ActualNormalCompressionResponse
import GlobalEmbedding.Paper.SmoothFrameNormalProjection
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Joint regularity of the same explicit ambient polar operator

Regularity is a conclusion about the fixed binomial-series formula. Actual
frame families supply their genuine normal projections through the existing
Gram-projection theorem; no smoothness of a chosen identification is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private noncomputable local instance smoothOperatorSemi : SeminormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance smoothOperatorNormed : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance smoothOperatorSpace : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

section NormedBase
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem contDiffOn_actualPolarOperator (P R : X → V →L[ℝ] V) (s : Set X)
    (hP : ContDiffOn ℝ ∞ P s) (hR : ContDiffOn ℝ ∞ R s)
    (hgap : ∀ x ∈ s, ‖P x - R x‖ < 1) :
    ContDiffOn ℝ ∞ (fun x ↦ actualPolarOperator (P x) (R x)) s := by
  intro x hx
  exact (contDiffAt_actualPolarPair (P x, R x) (hgap x hx)).comp_contDiffWithinAt x
    ((hP x hx).prodMk (hR x hx))

/-- Joint smooth actual frames, for example `X = Parameters × SourceChart`,
give joint smoothness of the actual normal identification operator. -/
theorem contDiffOn_actualFramePolarOperator
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D]
    (A₀ A : X → D →L[ℝ] V) (s : Set X)
    (hA₀ : ContDiffOn ℝ ∞ A₀ s) (hA : ContDiffOn ℝ ∞ A s)
    (hi₀ : ∀ x ∈ s, Function.Injective (A₀ x))
    (hi : ∀ x ∈ s, Function.Injective (A x))
    (hgap : ∀ x ∈ s,
      ‖(LinearMap.range (A₀ x).toLinearMap)ᗮ.starProjection -
        (LinearMap.range (A x).toLinearMap)ᗮ.starProjection‖ < 1) :
    ContDiffOn ℝ ∞ (fun x ↦ actualPolarOperator
      (LinearMap.range (A₀ x).toLinearMap)ᗮ.starProjection
      (LinearMap.range (A x).toLinearMap)ᗮ.starProjection) s := by
  exact contDiffOn_actualPolarOperator _ _ s
    (smooth_frame_normal_projection A₀ hA₀ hi₀)
    (smooth_frame_normal_projection A hA hi) hgap

/-- With the genuine common metric, a first-jet closeness budget supplies the
projection gap needed by the same explicit joint smooth operator. -/
theorem contDiffOn_actualFramePolarOperator_of_firstJet_gap
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D]
    (A₀ A : X → D →L[ℝ] V) (s : Set X)
    (hA₀ : ContDiffOn ℝ ∞ A₀ s) (hA : ContDiffOn ℝ ∞ A s)
    (hi₀ : ∀ x ∈ s, Function.Injective (A₀ x))
    (hi : ∀ x ∈ s, Function.Injective (A x))
    (hmetric : ∀ x ∈ s, (A x).adjoint.comp (A x) = (A₀ x).adjoint.comp (A₀ x))
    (hgap : ∀ x ∈ s,
      ‖((A₀ x).adjoint.comp (A₀ x)).inverse‖ *
        (‖A x‖ + ‖A₀ x‖) * ‖A x - A₀ x‖ < 1) :
    ContDiffOn ℝ ∞ (fun x ↦ actualPolarOperator
      (LinearMap.range (A₀ x).toLinearMap)ᗮ.starProjection
      (LinearMap.range (A x).toLinearMap)ᗮ.starProjection) s := by
  apply contDiffOn_actualFramePolarOperator A₀ A s hA₀ hA hi₀ hi
  intro x hx
  rw [norm_sub_rev]
  exact (norm_actualNormalProjection_sub_fixed_metric_le (A x) (A₀ x)
    (hi x hx) (hi₀ x hx) (hmetric x hx)).trans_lt (hgap x hx)

end NormedBase

section ManifoldBase
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- This theorem applies on the original parameter/source product manifold
and its original domain. It does not restrict the parameter ball or replace
the normal projections. -/
theorem contMDiffOn_actualPolarOperator
    (P R : M → V →L[ℝ] V) (s : Set M)
    (hP : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] V) ∞ P s)
    (hR : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] V) ∞ R s)
    (hgap : ∀ x ∈ s, ‖P x - R x‖ < 1) :
    ContMDiffOn I 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun x ↦ actualPolarOperator (P x) (R x)) s := by
  intro x hx
  exact (contDiffAt_actualPolarPair (P x, R x) (hgap x hx)).comp_contMDiffWithinAt
    (f := fun y : M ↦ (P y, R y)) ((hP x hx).prodMk_space (hR x hx))

end ManifoldBase

end GlobalEmbedding.NormalPolar
