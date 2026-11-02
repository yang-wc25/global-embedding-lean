import Smoothing.TensorLocalFieldSmoothing
import Smoothing.ParameterLocalProduct

/-!
# Actual native tensor smoothing on a local parameter chart family

The finite parameter family need not cover the whole parameter manifold.
The output is a genuine bilinear form on the original source tangent fiber.
Its joint original coordinates are smooth, with the full native frame change
derived from the source atlas. No independent frame regularity premise and
no global parameter-cover premise occur in the final theorem.

This file supplies construction, native-coordinate identity, and regularity.
The actual local chart-maximum tail and gain are developed in
`TensorLocalOriginal` and `TensorLocalOriginalGain`. Their source budgets are
on genuine fixed sampling neighborhoods, not automatically on K alone.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper
  GlobalEmbedding.Continuation Function Set Filter
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance tensorLocalParameterChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance tensorLocalParameterManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

/-- Source tangent slots remain spatial even though convolution is joint. -/
def tensorLocalParameterFrame
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count × Fin pcount) (z : P × M) :
    Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) z.2) :=
  bufferedNativeTensorFrame A hA i.1 z.2

theorem tensorLocalParameterFrameTransition_eq_source
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (p i : Fin A.count × Fin pcount) (a r : Fin n) :
    tensorLocalFrameTransition (parameterLocalProductFamily A B)
      (tensorLocalParameterFrame A B hA) p i a r =
    tensorFrameTransition A (bufferedNativeTensorFrame A hA) p.1 i.1 a r ∘ Prod.snd := rfl

/-- Actual native transitions are jointly smooth with no parameter-cover
assumption and no independently postulated frame field. -/
theorem tensorLocalParameterFrameTransition_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (p i : Fin A.count × Fin pcount) (a r : Fin n) :
    ContDiffOn ℝ ∞ (tensorLocalFrameTransition (parameterLocalProductFamily A B)
      (tensorLocalParameterFrame A B hA) p i a r)
      (tensorLocalChartOverlap (parameterLocalProductFamily A B) p i) := by
  rw [tensorLocalParameterFrameTransition_eq_source]
  exact (tensorNativeFrameTransition_contDiffOn A hA p.1 i.1 a r).comp
    contDiff_snd.contDiffOn (fun _ hy => ⟨hy.1.2, hy.2.2⟩)

/-- Exact frozen original source-first native tensor coefficients. -/
theorem tensorLocalParameterCoordinates_eq_original
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (i : Fin A.count × Fin pcount) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B.chart i) :
    tensorLocalFieldCoefficients (tensorLocalParameterFrame A B hA)
      (fun z => H z.1 z.2) i
      (((parameterLocalProductFamily A B).chart i).symm ((parameterTensorModelEquiv n d).symm y)) =
      incrementsOriginalTensorCoordinates A B.chart H i y := by
  exact (incrementsOriginalTensorCoordinates_eq_nativeFrame A hA B.chart H i y hy).symm

/-- Original own-chart regularity supplies precisely the coefficient field
that is integrated by the actual local smoothing operator. -/
theorem tensorLocalParameterInput_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i)) (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞
      (tensorLocalFieldCoefficients (tensorLocalParameterFrame A B hA)
        (fun z => H z.1 z.2) i ∘ ((parameterLocalProductFamily A B).chart i).symm)
      ((parameterLocalProductFamily A B).chart i).target := by
  let c := parameterTensorModelEquiv n d
  have hmap : MapsTo c ((parameterLocalProductFamily A B).chart i).target
      (incrementsOriginalDifferentiation A B.chart i) := by
    intro z hz
    rw [← parameterLocalProduct_targets A B i]
    change c.symm (c z) ∈ ((parameterLocalProductFamily A B).chart i).target
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz
  apply ((hH i).comp c.contDiff.contDiffOn hmap).congr
  intro z hz
  have h := tensorLocalParameterCoordinates_eq_original A B hA H i (c z) (hmap hz)
  simpa only [Function.comp_apply, c, ContinuousLinearEquiv.symm_apply_apply] using h

/-- The actual joint integral reconstructs a source tangent tensor. -/
def tensorLocalParameterSmoothing
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    (K : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) → ℝ)
    (ell : ℝ) (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (p : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  tensorLocalFieldSmoothing (parameterLocalProductFamily A B) mu K ell chi
    (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2) (p,x)

/-- True joint smoothness in the exact original tensor ABI. All native frame
regularity is derived, and the parameter charts may cover only a neighborhood
of the original compact parameter set. -/
theorem tensorLocalParameterSmoothing_original_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A)
    (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    [mu.IsAddHaarMeasure]
    {K : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hsupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i)) (i : Fin A.count × Fin pcount) :
    ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart
      (tensorLocalParameterSmoothing A B hA mu K ell chi H) i)
      (incrementsOriginalDifferentiation A B.chart i) := by
  have hout := tensorLocalFieldSmoothing_coordinates_contDiffOn
    (parameterLocalProductFamily A B) (parameterLocalProductFamily_chart_mem A B hA hB)
    mu hK hcompact hsupp hrho hell hell1 chi hchi hsupport
    (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2)
    (tensorLocalParameterInput_contDiffOn A B hA H hH)
    (tensorLocalParameterFrameTransition_contDiffOn A B hA) i
  let c := parameterTensorModelEquiv n d
  have hmap : MapsTo c.symm (incrementsOriginalDifferentiation A B.chart i)
      ((parameterLocalProductFamily A B).chart i).target := by
    intro y hy
    exact (congrArg (fun s => y ∈ s) (parameterLocalProduct_targets A B i)).mpr hy
  apply (hout.comp c.symm.contDiff.contDiffOn hmap).congr
  intro y hy
  exact (tensorLocalParameterCoordinates_eq_original A B hA
    (tensorLocalParameterSmoothing A B hA mu K ell chi H) i y hy).symm

#print axioms tensorLocalParameterFrameTransition_contDiffOn
#print axioms tensorLocalParameterCoordinates_eq_original
#print axioms tensorLocalParameterSmoothing_original_contDiffOn

end
end GlobalEmbedding.Offline
