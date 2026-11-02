import GlobalEmbedding.Paper.SmoothCoframeNormalization
import GlobalEmbedding.Paper.ManifoldFiniteOperatorSmoothness
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Actual smooth chart coefficients of the normalized coframe

The global covectors come from the existing positive metric-root construction.
Their coordinate coefficients are obtained by applying those covectors to the
actual derivative of a chart inverse. Smoothness is proved through the genuine
tangent map and vector-bundle evaluation, not postulated for an abstract field.
-/

noncomputable section
open Bundle Manifold Set
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Pull back an actual smooth cotangent section by an actual coordinate map. -/
def coordinateCovector
    (θ : ContMDiffSection I (E →L[ℝ] ℝ) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))
    (φ : V → M) (y : V) : V →L[ℝ] ℝ :=
  (θ (φ y)).comp (mfderiv 𝓘(ℝ, V) I φ y)

theorem coordinateCovector_contDiffOn
    (θ : ContMDiffSection I (E →L[ℝ] ℝ) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))
    (φ : V → M) {O : Set V} (hO : IsOpen O)
    (hφ : ContMDiffOn 𝓘(ℝ, V) I ∞ φ O) :
    ContDiffOn ℝ ∞ (coordinateCovector I θ φ) O := by
  apply contDiffOn_clm_apply.mpr
  intro v y hy
  have hp : ContMDiffAt 𝓘(ℝ, V) I ∞ φ y :=
    (hφ y hy).contMDiffAt (hO.mem_nhds hy)
  have hv : ContMDiffAt 𝓘(ℝ, V) (𝓘(ℝ, V)).tangent ∞
      (fun z : V ↦ (TotalSpace.mk' V z v : TangentBundle 𝓘(ℝ, V) V)) y := by
    exact (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
      (𝕜 := ℝ) (E := V) (V := fun _ : V ↦ v)).mpr contDiffWithinAt_const
  have ht := (hp.contMDiffAt_tangentMap (X := TotalSpace.mk' V y v)
    (m := ∞) (by simp)).comp y hv
  have hθ := θ.contMDiff.contMDiffAt.comp y hp
  have he := ContMDiffAt.clm_bundle_apply
    (F₁ := E) (F₂ := ℝ)
    (E₁ := (TangentSpace I : M → Type _)) (E₂ := fun _ : M ↦ ℝ)
    (b := φ) (ϕ := fun z ↦ θ (φ z))
    (v := fun z ↦ mfderiv 𝓘(ℝ, V) I φ z v) hθ ht
  simp only [contMDiffAt_totalSpace] at he
  exact he.2.contDiffAt.contDiffWithinAt

variable [FiniteDimensional ℝ E] {n : ℕ}

/-- The actual normalized coframe applied to the actual coordinate derivative.
The output retains the canonical real Euclidean L² norm. -/
def coordinateOrthonormalCoframe
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (φ : V → M) (y : V) :
    V →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (positiveRootCoframe I g f (φ y)).toLinearMap.toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, V) I φ y)

theorem coordinateOrthonormalCoframe_apply
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (φ : V → M) (y v : V) :
    coordinateOrthonormalCoframe I g f φ y v =
      WithLp.toLp 2 (fun i ↦ coordinateCovector I (positiveRootDualSection I g f i) φ y v) := by
  ext i
  exact positiveRootCoframe_apply_eq_dual I g f (φ y)
    (mfderiv 𝓘(ℝ, V) I φ y v) i

/-- The actual smooth metric and frame produce smooth coordinate coframe
coefficients on every open smooth coordinate domain. -/
theorem coordinateOrthonormalCoframe_contDiffOn
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (φ : V → M)
    {O : Set V} (hO : IsOpen O) (hφ : ContMDiffOn 𝓘(ℝ, V) I ∞ φ O) :
    ContDiffOn ℝ ∞ (coordinateOrthonormalCoframe I g f φ) O := by
  apply contDiffOn_clm_apply.mpr
  intro v
  have hc : ContDiffOn ℝ ∞
      (fun y : V ↦ fun i : Fin n ↦
        coordinateCovector I (positiveRootDualSection I g f i) φ y v) O :=
    contDiffOn_pi.mpr fun i ↦
      (coordinateCovector_contDiffOn I (positiveRootDualSection I g f i) φ hO hφ).clm_apply
        contDiffOn_const
  convert PiLp.contDiff_toLp.comp_contDiffOn hc using 1
  funext y
  exact coordinateOrthonormalCoframe_apply I g f φ y v

/-- Its exact Gram is the pullback of the original metric, with no arbitrary
replacement metric or norm-equivalence assumption. -/
theorem coordinateOrthonormalCoframe_metric
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : FullTangentFrame I (M := M) n) (φ : V → M) (y v w : V) :
    inner ℝ (coordinateOrthonormalCoframe I g f φ y v)
      (coordinateOrthonormalCoframe I g f φ y w) =
      g.inner (φ y) (mfderiv 𝓘(ℝ, V) I φ y v) (mfderiv 𝓘(ℝ, V) I φ y w) :=
  positiveRootCoframe_isometry I g f (φ y) _ _

end GlobalEmbedding.Initialization
