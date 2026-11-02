import Initialization.Assembly.ChartCoframe
import Initialization.Geometry.CoframeFreezing
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Actual invertible normalized coefficients in a smooth chart

The coefficient field is obtained from the original metric and tangent frame.
Both its smoothness and invertibility are proved from a genuine maximal-atlas
chart. Compactness then supplies all derivative bounds and an inverse bound,
before any oscillation parameter is chosen.
-/

noncomputable section
open Bundle Manifold Set IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

def chartOrthonormalCoframe
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E) : E → E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  coordinateOrthonormalCoframe 𝓘(ℝ, E) g f e.symm

theorem chartOrthonormalCoframe_contDiffOn
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (chartOrthonormalCoframe g f e) e.target :=
  coordinateOrthonormalCoframe_contDiffOn 𝓘(ℝ, E) g f e.symm e.open_target
    (contMDiffOn_symm_of_mem_maximalAtlas he)

theorem chartOrthonormalCoframe_bijective
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target) :
    Function.Bijective (chartOrthonormalCoframe g f e y) := by
  have hd : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  exact (positiveRootCoframe 𝓘(ℝ, E) g f (e.symm y)).bijective.comp
    (hd.symm.mfderiv_bijective hy)

/-- An actual chart coframe equivalence, not a further input datum. -/
def chartOrthonormalCoframeEquiv
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (y : E) (hy : y ∈ e.target) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.ofBijective (chartOrthonormalCoframe g f e y).toLinearMap
    (chartOrthonormalCoframe_bijective g f e he hy)).toContinuousLinearEquiv

@[simp] theorem chartOrthonormalCoframeEquiv_coe
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (y : E) (hy : y ∈ e.target) :
    (chartOrthonormalCoframeEquiv g f e he y hy : E →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      chartOrthonormalCoframe g f e y := rfl

theorem chartOrthonormalCoframe_inverse_contDiffOn
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (fun y ↦ (chartOrthonormalCoframe g f e y).inverse) e.target := by
  intro y hy
  have hi : (chartOrthonormalCoframe g f e y).IsInvertible :=
    ⟨chartOrthonormalCoframeEquiv g f e he y hy, rfl⟩
  exact (hi.contDiffAt_map_inverse.comp y
    ((chartOrthonormalCoframe_contDiffOn g f e he).contDiffAt
      (e.open_target.mem_nhds hy))).contDiffWithinAt

/-- The actual metric-normalized chart coefficients supply their own uniform
derivative and inverse budgets on each compact coordinate core. Empty cores
are permitted. No bound or positive margin is assumed. -/
theorem exists_chartOrthonormalCoframe_bounds
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {s : Set E} (hs : IsCompact s) (hsE : s ⊆ e.target) :
    ∃ (B : ℕ → ℝ) (L : ℝ),
      (∀ j, 0 < B j) ∧ 0 < L ∧
      (∀ j y, y ∈ s → ‖iteratedFDeriv ℝ j (chartOrthonormalCoframe g f e) y‖ ≤ B j) ∧
      (∀ y (hy : y ∈ s),
        ‖((chartOrthonormalCoframeEquiv g f e he y (hsE hy)).symm :
          EuclideanSpace ℝ (Fin n) →L[ℝ] E)‖ ≤ L) := by
  obtain ⟨B, hB, hbound⟩ := exists_compact_smooth_derivative_bounds hs e.open_target hsE
    (chartOrthonormalCoframe g f e) (chartOrthonormalCoframe_contDiffOn g f e he)
  obtain ⟨L, hL⟩ := hs.bddAbove_image
    (((chartOrthonormalCoframe_inverse_contDiffOn g f e he).continuousOn.norm).mono hsE)
  refine ⟨fun j ↦ B j + 1, max 0 L + 1, ?_, by positivity, ?_, ?_⟩
  · intro j
    linarith [hB j]
  · intro j y hy
    exact (hbound j y hy).trans (by linarith)
  · intro y hy
    have hb := hL ⟨y, hy, rfl⟩
    have hi : (chartOrthonormalCoframe g f e y).inverse =
        ((chartOrthonormalCoframeEquiv g f e he y (hsE hy)).symm :
          EuclideanSpace ℝ (Fin n) →L[ℝ] E) := by
      exact ContinuousLinearMap.inverse_equiv
        (chartOrthonormalCoframeEquiv g f e he y (hsE hy))
    change ‖(chartOrthonormalCoframe g f e y).inverse‖ ≤ L at hb
    rw [hi] at hb
    exact hb.trans (by linarith [le_max_right (0 : ℝ) L])

end GlobalEmbedding.Initialization
