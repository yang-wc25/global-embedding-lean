import Initialization.Assembly.ChartCoframeEquiv

/-!
# Exact coordinate naturality of the actual normalized coframe

The same global positive-root coframe is used in all charts. Its coefficients
therefore transform by the actual derivative of the chart transition. This
identity is proved from the manifold chain rule and the genuine inverse-chart
identity; no compatibility of abstract coefficient fields is postulated.
-/

noncomputable section
open Bundle Manifold Set IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

/-- Maximal-atlas smoothness supplies both genuine chart derivatives. -/
theorem initialization_chart_mdifferentiable
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) :
    e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩

/-- The actual derivative of the true transition is the composition of the
two actual manifold derivatives on their genuine overlap. -/
theorem initialization_chart_transition_fderiv
    (e e₀ : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : E} (hy : y ∈ e₀.target) (hp : e₀.symm y ∈ e.source) :
    fderiv ℝ (e ∘ e₀.symm) y =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e₀.symm y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm y) := by
  have hc := mfderiv_comp y
    ((initialization_chart_mdifferentiable e he).mdifferentiableAt hp)
    ((initialization_chart_mdifferentiable e₀ he₀).mdifferentiableAt_symm hy)
  have hf := mfderiv_eq_fderiv (𝕜 := ℝ) (f := e ∘ e₀.symm) (x := y)
  ext v
  have hcv := congrArg (fun A ↦ A v) hc
  have hfv := congrArg (fun A ↦ A v) hf
  exact hfv.symm.trans hcv

/-- Exact coframe coordinate transformation, with the actual reference chart
and the actual patch chart. This is the cancellation behind the cross-chart
frozen phase-rate error. -/
theorem chartOrthonormalCoframe_naturality
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e e₀ : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : E} (hy : y ∈ e₀.target) (hp : e₀.symm y ∈ e.source) :
    (chartOrthonormalCoframe g f e (e (e₀.symm y))).comp
      (fderiv ℝ (e ∘ e₀.symm) y) = chartOrthonormalCoframe g f e₀ y := by
  rw [initialization_chart_transition_fderiv e e₀ he he₀ hy hp]
  apply ContinuousLinearMap.ext
  intro v
  change positiveRootCoframe 𝓘(ℝ, E) g f (e.symm (e (e₀.symm y)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (e₀.symm y))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e₀.symm y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm y v))) =
    positiveRootCoframe 𝓘(ℝ, E) g f (e₀.symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm y v)
  have hinv := congrArg (fun A ↦ A
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm y v))
      ((initialization_chart_mdifferentiable e he).symm_comp_deriv hp)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (e₀.symm y))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e₀.symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm y v)) =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm y v at hinv
  rw [hinv]
  exact congrArg (fun p : M ↦ positiveRootCoframe 𝓘(ℝ, E) g f p
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e₀.symm y v)) (e.left_inv hp)

/-- The actual cross-chart discrepancy factors through the actual frozen
coframe discrepancy and the actual transition derivative. -/
theorem chartOrthonormalCoframe_frozen_transition_error
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, E) (M := M) n)
    (e e₀ : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : E) {y : E} (hy : y ∈ e₀.target) (hp : e₀.symm y ∈ e.source) :
    (chartOrthonormalCoframe g f e p).comp (fderiv ℝ (e ∘ e₀.symm) y) -
      chartOrthonormalCoframe g f e₀ y =
    (chartOrthonormalCoframe g f e p -
      chartOrthonormalCoframe g f e (e (e₀.symm y))).comp
        (fderiv ℝ (e ∘ e₀.symm) y) := by
  rw [ContinuousLinearMap.sub_comp, chartOrthonormalCoframe_naturality g f e e₀ he he₀ hy hp]

end GlobalEmbedding.Initialization
