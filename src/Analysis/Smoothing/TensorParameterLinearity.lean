import Smoothing.TensorParameterSmoothing

/-!
# One actual linear operator on the original parameterized tensor fields

The domain consists of genuine native source-tangent bilinear fields whose
frozen original coordinate functions are jointly smooth. The same integral
formula used in the original (6.4), gain and positivity theorems is a linear
endomorphism of that space. Smoothness of its output is proved by the actual
chart/frame construction, rather than included as additional data.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance tensorParameterLinearityChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance tensorParameterLinearityManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

/-- The original joint smooth tensor space; no surrogate coefficient fields
and no positivity constraint (which would fail to be a linear subspace). -/
def originalSmoothParameterTensorFields
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) :
    Submodule ℝ ((p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) where
  carrier H := ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
    (incrementsOriginalDifferentiation A B.chart i)
  zero_mem' := by
    intro i
    change ContDiffOn ℝ ∞ (fun _ : Fin (n + d) → ℝ => (0 : Fin (n * n) → ℝ)) _
    exact contDiffOn_const
  add_mem' := by
    intro H L hH hL i
    exact (hH i).add (hL i)
  smul_mem' := by
    intro c H hH i
    exact (hH i).const_smul c

/-- Actual integral additivity for smooth original native tensor fields. -/
theorem parameterNativeTensorSmoothing_add
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))) [mu.IsAddHaarMeasure]
    {K : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    (H L : originalSmoothParameterTensorFields A B) :
    parameterNativeTensorSmoothing A B hA mu K ell chi (H + L) =
      parameterNativeTensorSmoothing A B hA mu K ell chi H +
        parameterNativeTensorSmoothing A B hA mu K ell chi L := by
  have h := bufferedTensorSmoothing_add (parameterProductAtlas A B) mu hK hcompact hsupp
    hrho hell hell1 chi hchiSupport (parameterTensorNativeFrame A B hA)
    (fun z => H.val z.1 z.2) (fun z => L.val z.1 z.2)
    (parameterTensorNativeCoordinates_contDiffOn A B hA H H.property)
    (parameterTensorNativeCoordinates_contDiffOn A B hA L L.property)
  funext p x
  exact congrFun h (p, x)

/-- Actual scalar linearity needs no extra integrability premise. -/
theorem parameterNativeTensorSmoothing_smul
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → ℝ)
    (ell : ℝ) (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) (c : ℝ) :
    parameterNativeTensorSmoothing A B hA mu K ell chi (c • H) =
      c • parameterNativeTensorSmoothing A B hA mu K ell chi H := by
  have h := bufferedTensorSmoothing_smul (parameterProductAtlas A B) mu K ell chi
    (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2) c
  funext p x
  exact congrFun h (p, x)

/-- The SAME native operator of the tail/gain theorems, now a proved linear
endomorphism of the ORIGINAL coefficient-smooth tensor space. -/
def parameterNativeTensorSmoothingLinearMap
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))) [mu.IsAddHaarMeasure]
    {K : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i) :
    originalSmoothParameterTensorFields A B →ₗ[ℝ] originalSmoothParameterTensorFields A B where
  toFun H := ⟨parameterNativeTensorSmoothing A B hA mu K ell chi H,
    parameterNativeTensorSmoothing_contDiffOn A B hA hB mu hK hcompact hsupp hrho hell hell1
      chi hchi hchiSupport H H.property⟩
  map_add' H L := by
    apply Subtype.ext
    exact parameterNativeTensorSmoothing_add A B hA mu hK hcompact hsupp hrho hell hell1
      chi hchiSupport H L
  map_smul' c H := by
    apply Subtype.ext
    exact parameterNativeTensorSmoothing_smul A B hA mu K ell chi H c

end
end GlobalEmbedding.Offline
