import GlobalEmbedding.Paper.FinitePositiveSpanStability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The actual sixteen angular-cone limiting samples and their robust margin

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines327–332.
DAG node: `cone-finite-span-stability`.
-/
noncomputable section
open Set Metric
open scoped RealInnerProductSpace
namespace GlobalEmbedding.Paper

/-- The actual four-dimensional Euclidean angular-cone target. -/
abbrev MatrixAngularSpace := EuclideanSpace ℝ (Fin 4)

/-- Two cosine levels, four consecutive quarter-turn phases, and both true signs. -/
abbrev MatrixAngularSample := (Fin 2 × Fin 4) × Bool

/-- The actual unsigned limiting sample. -/
def matrixAngularBase (c₀ c₁ : ℝ) (j : Fin 2) (k : Fin 4) : MatrixAngularSpace :=
  WithLp.toLp 2 ![Real.sin ((k : ℝ) * Real.pi / 2),
    Real.cos ((k : ℝ) * Real.pi / 2), ![c₀, c₁] j, 1]

/-- The original sixteen limiting angular vectors, with the genuine plus/minus signs. -/
def matrixAngularTemplate (c₀ c₁ : ℝ) (i : MatrixAngularSample) : MatrixAngularSpace :=
  if i.2 then matrixAngularBase c₀ c₁ i.1.1 i.1.2
  else -matrixAngularBase c₀ c₁ i.1.1 i.1.2

/-- The true sixteen angular samples have positive support in every nonzero direction.
Opposite phase differences kill the first two coordinates; the two distinct cosine
levels then kill the last two. This proves actual positive spanning, not just a rank claim. -/
theorem matrixAngularTemplate_positive_support (c₀ c₁ : ℝ) (hc : c₀ ≠ c₁)
    (ξ : MatrixAngularSpace) (hξ : ξ ≠ 0) :
    ∃ i : MatrixAngularSample, 0 < ⟪ξ, matrixAngularTemplate c₀ c₁ i⟫ := by
  classical
  by_contra hbad
  push Not at hbad
  have hz (j : Fin 2) (k : Fin 4) : ⟪ξ, matrixAngularBase c₀ c₁ j k⟫ = 0 := by
    have hp := hbad ((j, k), true)
    have hn := hbad ((j, k), false)
    simp [matrixAngularTemplate] at hp hn
    linarith
  have h00 := hz 0 0
  have h01 := hz 0 1
  have h02 := hz 0 2
  have h10 := hz 1 0
  have hpi : (2 : ℝ) * Real.pi / 2 = Real.pi := by ring
  simp [matrixAngularBase, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.vecHead, Matrix.vecTail, hpi] at h00 h01 h02 h10
  have hx₁ : ξ 1 = 0 := by linarith
  have hx₀ : ξ 0 = 0 := by linarith
  have hx₂prod : (c₀ - c₁) * ξ 2 = 0 := by nlinarith
  have hx₂ : ξ 2 = 0 := (mul_eq_zero.mp hx₂prod).resolve_left (sub_ne_zero.mpr hc)
  have hx₃ : ξ 3 = 0 := by simpa only [hx₁, hx₂, mul_zero, zero_add] using h00
  apply hξ
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [hx₀, hx₁, hx₂, hx₃]

/-- The original sixteen angular samples have a genuine robust convex-ball margin:
any sixteen actual nearby vectors still contain a fixed Euclidean ball in their
convex hull and satisfy the same quantitative positive-support inequality. -/
theorem matrixAngularTemplate_stable (c₀ c₁ : ℝ) (hc : c₀ ≠ c₁) :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ ∀ w : MatrixAngularSample → MatrixAngularSpace,
      (∀ i, ‖w i - matrixAngularTemplate c₀ c₁ i‖ ≤ ε) →
      (∀ ξ : MatrixAngularSpace, ‖ξ‖ = 1 → ∃ i, r ≤ ⟪ξ, w i⟫) ∧
      closedBall (0 : MatrixAngularSpace) r ⊆ convexHull ℝ (range w) :=
  finite_positive_span_stable (matrixAngularTemplate c₀ c₁)
    (matrixAngularTemplate_positive_support c₀ c₁ hc)

/-- In particular the genuine sixteen limiting samples themselves contain a ball. -/
theorem matrixAngularTemplate_ball (c₀ c₁ : ℝ) (hc : c₀ ≠ c₁) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : MatrixAngularSpace) r ⊆
      convexHull ℝ (range (matrixAngularTemplate c₀ c₁)) := by
  obtain ⟨ε, r, hε, hr, hw⟩ := matrixAngularTemplate_stable c₀ c₁ hc
  exact ⟨r, hr, (hw _ (fun _ ↦ by simpa using hε.le)).2⟩

end GlobalEmbedding.Paper
