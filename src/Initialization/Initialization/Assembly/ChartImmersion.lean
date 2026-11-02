import Initialization.Assembly.ChartCoframeNaturality
import GlobalEmbedding.Paper.BufferedAtlas

/-!
# Actual coordinate injectivity gives immersion of the same manifold map

The argument uses the real inverse-chart derivative and its surjectivity.
There is no assumption that a chart representative is smooth outside its target,
and no identification of the scaled coordinate norm with a manifold metric norm.
-/

noncomputable section
open Manifold Set IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The true coordinate derivative is the actual manifold derivative composed
with the actual derivative of the inverse chart, on its genuine target. -/
theorem initialization_coordinate_fderiv_apply
    (H : M → V) (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : E} (hy : y ∈ e.target) (v : E) :
    fderiv ℝ (H ∘ e.symm) y v =
      mvfderiv 𝓘(ℝ, E) H (e.symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y v) := by
  have hc := mvfderiv_comp y (hH.contMDiffAt.mdifferentiableAt (by simp))
    ((initialization_chart_mdifferentiable e he).mdifferentiableAt_symm hy)
  have hf := mvfderiv_eq_fderiv (𝕜 := ℝ) (f := H ∘ e.symm) (x := y)
  exact (congrArg (fun A ↦ A v) hf).symm.trans (congrArg (fun A ↦ A v) hc)

/-- Coordinate injectivity is enough for the original manifold differential.
This is an exact invariance statement, so it uses no norm comparison. -/
theorem initialization_mvfderiv_injective_of_chart
    (H : M → V) (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : E} (hy : y ∈ e.target)
    (hinj : Function.Injective (fderiv ℝ (H ∘ e.symm) y)) :
    Function.Injective (mvfderiv 𝓘(ℝ, E) H (e.symm y)) := by
  intro v w h
  have hs : Function.Surjective (fun u : E ↦
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y u) :=
    ((initialization_chart_mdifferentiable e he).symm.mfderiv_bijective hy).2
  obtain ⟨v', hv⟩ := hs v
  obtain ⟨w', hw⟩ := hs w
  have heq : fderiv ℝ (H ∘ e.symm) y v' = fderiv ℝ (H ∘ e.symm) y w' := by
    exact (initialization_coordinate_fderiv_apply H hH e he hy v').trans
      ((congrArg (mvfderiv 𝓘(ℝ, E) H (e.symm y)) hv).trans
        (h.trans ((congrArg (mvfderiv 𝓘(ℝ, E) H (e.symm y)) hw).symm.trans
          (initialization_coordinate_fderiv_apply H hH e he hy w').symm)))
  have hvw := hinj heq
  exact hv.symm.trans ((congrArg (fun u : E ↦
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y u) hvw).trans hw)

/-- A genuine covering buffered atlas transfers all coordinate immersion
conclusions to the same global map, including disconnected and empty sources. -/
theorem initialization_mvfderiv_injective_of_bufferedAtlas
    (H : M → V) (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ H)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hinj : ∀ i y, y ∈ (A.chart i).target →
      Function.Injective (fderiv ℝ (H ∘ (A.chart i).symm) y)) :
    ∀ x, Function.Injective (mvfderiv 𝓘(ℝ, E) H x) := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  have hs := A.inner_subset i hi
  have h := initialization_mvfderiv_injective_of_chart H hH (A.chart i) (hA.chart_mem i)
    ((A.chart i).map_source hs) (hinj i _ ((A.chart i).map_source hs))
  intro v w hvw
  apply h
  have heq := (A.chart i).left_inv hs
  convert hvw using 1 <;> rw [heq]

end GlobalEmbedding.Initialization
