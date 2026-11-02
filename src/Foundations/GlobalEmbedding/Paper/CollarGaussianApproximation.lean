import GlobalEmbedding.Paper.CollarGaussianEntireExtension
import GlobalEmbedding.Paper.CollarGaussianConvergenceCk
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The complete source Gaussian approximation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof line 520. The real and complex kernels have exactly the source width normalization.
-/

open MeasureTheory Filter Metric Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The actual coordinatewise complexification of a real Euclidean vector, with its original
Euclidean norm. Source: Proposition `prop:collar`, proof line 520, real restriction of the
complex Gaussian integral. This is explicit real-linear isometric data in every dimension. -/
def collarGaussianRealToComplex (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun x := WithLp.toLp 2 (fun j ↦ (x j : ℂ))
  map_add' x y := by ext j; simp
  map_smul' r x := by ext j; simp [Complex.real_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq]

/-- Actual coordinate values of the canonical Euclidean complexification.
Proof: evaluation of its explicit coordinatewise real embedding. -/
theorem collarGaussianRealToComplex_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : collarGaussianRealToComplex n x j = (x j : ℂ) := rfl

/-- The original source normalized Gaussian approximations have actual entire complex
extensions, their exact real restrictions, and convergence in every global Ck supremum norm.

Source: Proposition `prop:collar`, proof line 520.
Use the already proved entire-extension and Gaussian Ck convergence theorems with their actual
kernels. Coordinatewise real embedding is an actual linear isometry, so it commutes with the
Bochner integral. On a real input the sum of the complex coordinate squares is the real
Euclidean squared norm, and the complex exponential is the real exponential's cast. The actual
PiLp coordinate equivalence preserves Lebesgue volume, so the product-coordinate integral in
the entire extension is exactly the embedded Euclidean convolution. This proves the exact
real restriction without any unproved measure convention. The previously proved global
all-order Gaussian approximation supplies smoothness and each actual Ck double-supremum limit.
All dimensions and derivative orders may be zero. No fixed support or extra regularity of an
unprovided parameter family, analyticity of f, or geometric free-map data is assumed. -/
theorem collar_gaussian_approximation {d N : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    let G : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) := fun ε x ↦
      ∫ y : EuclideanSpace ℝ (Fin d),
        ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • f y
    let F : ℝ → EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin N) := fun ε z ↦
      ∫ y : Fin d → ℝ,
        ((((Real.pi * ε) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(∑ i : Fin d, (z i - (y i : ℂ)) ^ 2) / (ε : ℂ))) •
            collarGaussianRealToComplex N (f (WithLp.toLp 2 y))
    (∀ ε : ℝ, 0 < ε → Differentiable ℂ (F ε) ∧
      (∀ x : EuclideanSpace ℝ (Fin d),
        F ε (collarGaussianRealToComplex d x) = collarGaussianRealToComplex N (G ε x)) ∧
      ContDiff ℝ ∞ (G ε)) ∧
    ∀ k : ℕ, Tendsto
      (fun ε : ℝ ↦ ⨆ n : Fin (k + 1), ⨆ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ n.val (G ε) x - iteratedFDeriv ℝ n.val f x‖)
      (𝓝[>] 0) (𝓝 0) := by
  let G : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N) := fun ε x ↦
    ∫ y : EuclideanSpace ℝ (Fin d),
      ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • f y
  let F : ℝ → EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin N) := fun ε z ↦
    ∫ y : Fin d → ℝ,
      ((((Real.pi * ε) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-(∑ i : Fin d, (z i - (y i : ℂ)) ^ 2) / (ε : ℂ))) •
          collarGaussianRealToComplex N (f (WithLp.toLp 2 y))
  change (∀ ε : ℝ, 0 < ε → Differentiable ℂ (F ε) ∧
    (∀ x, F ε (collarGaussianRealToComplex d x) = collarGaussianRealToComplex N (G ε x)) ∧
    ContDiff ℝ ∞ (G ε)) ∧ _
  have hck := collar_gaussian_convergence_Ck f hf hcompact
  refine ⟨?_, hck.2.2⟩
  intro ε hε
  refine ⟨collar_gaussian_entire_extension ε hε f hf hcompact, ?_, hck.1 ε hε⟩
  intro x
  have hi (y : Fin d → ℝ) :
      ((((Real.pi * ε) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (-(∑ i : Fin d,
            (collarGaussianRealToComplex d x i - (y i : ℂ)) ^ 2) / (ε : ℂ))) •
        collarGaussianRealToComplex N (f (WithLp.toLp 2 y)) =
      collarGaussianRealToComplex N
        ((((Real.pi * ε) ^ (-(d : ℝ) / 2)) *
          Real.exp (-‖x - WithLp.toLp 2 y‖ ^ 2 / ε)) • f (WithLp.toLp 2 y)) := by
    have hs : (∑ i : Fin d,
        (collarGaussianRealToComplex d x i - (y i : ℂ)) ^ 2) =
        ((‖x - WithLp.toLp 2 y‖ ^ 2 : ℝ) : ℂ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [collarGaussianRealToComplex]
    rw [hs]
    have hk : (((Real.pi * ε) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-((‖x - WithLp.toLp 2 y‖ ^ 2 : ℝ) : ℂ) / (ε : ℂ)) =
        ((((Real.pi * ε) ^ (-(d : ℝ) / 2)) *
          Real.exp (-‖x - WithLp.toLp 2 y‖ ^ 2 / ε) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hk, map_smul]
    ext j
    simp [collarGaussianRealToComplex_apply, Complex.real_smul]
  calc
    F ε (collarGaussianRealToComplex d x) = ∫ y : Fin d → ℝ,
        collarGaussianRealToComplex N
          ((((Real.pi * ε) ^ (-(d : ℝ) / 2)) *
            Real.exp (-‖x - WithLp.toLp 2 y‖ ^ 2 / ε)) • f (WithLp.toLp 2 y)) :=
      integral_congr_ae (ae_of_all _ hi)
    _ = ∫ y : EuclideanSpace ℝ (Fin d), collarGaussianRealToComplex N
        ((((Real.pi * ε) ^ (-(d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / ε)) • f y) :=
      (PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
        (fun y : EuclideanSpace ℝ (Fin d) ↦ collarGaussianRealToComplex N
          ((((Real.pi * ε) ^ (-(d : ℝ) / 2)) * Real.exp (-‖x - y‖ ^ 2 / ε)) • f y))
    _ = collarGaussianRealToComplex N (G ε x) :=
      (collarGaussianRealToComplex N).integral_comp_comm _

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarGaussianRealToComplex

#print axioms GlobalEmbedding.Paper.collar_gaussian_approximation
