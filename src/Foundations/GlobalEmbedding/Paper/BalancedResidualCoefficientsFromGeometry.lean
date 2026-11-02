import GlobalEmbedding.Paper.BalancedGeometrySmooth
import GlobalEmbedding.Paper.BalancedFixedResidualCoefficientsSmooth
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# The original Gram residual gives smooth fixed coefficients

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines371–378.
DAG node: `balanced-residual-coefficients-from-geometry`.
-/

open Set Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual residual hypothesis of `lem:balanced` already implies native smoothness
of both fixed coefficient matrices, with no added coefficient regularity assumption.

Proof: an open neighborhood of zero contains r/2 and r/4 for some r>0. Each actual
Gram slice is smooth entrywise by the actual smooth directional derivative theorem,
so subtract the constant identity entry and apply the accepted scalar two-slice
coefficient recovery to these two distinct nonzero admissible parameters.
No compactness, nonemptiness, frame, parameter derivatives or positive dimension are
needed. Source: the fixed S3,S4 residual in the original statement, lines371–378. -/
theorem balanced_residual_coefficients_from_geometry
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {a N : ℕ} (J : Set ℝ) (hJ : IsOpen J) (hzero : 0 ∈ J)
    (P : ℝ → M → EuclideanSpace ℝ (Fin N))
    (hP : ∀ ε, ε ∈ J → ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (P ε))
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (S3 S4 : M → Matrix (Fin a) (Fin a) ℝ)
    (hresidual : ∀ (ε : ℝ) (hε : ε ∈ J) (x : M),
      balancedGeometry (P ε) (hP ε hε) D x =
        1 + ε ^ 3 • S3 x + ε ^ 4 • S4 x) :
    ∀ i j, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ S3 x i j) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ S4 x i j) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hJ 0 hzero
  have hhalf : r / 2 ∈ J := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith)
  have hquarter : r / 4 ∈ J := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith)
  intro i j
  let R (ε : ℝ) (hε : ε ∈ J) : M → ℝ :=
    fun x ↦ balancedGeometry (P ε) (hP ε hε) D x i j - (1 : Matrix _ _ ℝ) i j
  have hsmooth (ε : ℝ) (hε : ε ∈ J) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (R ε hε) :=
    (balancedGeometry_entry_contMDiff (P ε) (hP ε hε) D i j).sub contMDiff_const
  have hR (ε : ℝ) (hε : ε ∈ J) (x : M) :
      R ε hε x = ε ^ 3 • S3 x i j + ε ^ 4 • S4 x i j := by
    dsimp only [R]
    rw [hresidual ε hε x]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  exact balanced_fixed_residual_coefficients_smooth
    (R (r / 2) hhalf) (R (r / 4) hquarter) (fun x ↦ S3 x i j) (fun x ↦ S4 x i j)
    (r / 2) (r / 4) (by positivity) (by positivity) (by linarith)
    (hsmooth (r / 2) hhalf) (hsmooth (r / 4) hquarter)
    (hR (r / 2) hhalf) (hR (r / 4) hquarter)

#print axioms balanced_residual_coefficients_from_geometry

end GlobalEmbedding.Paper
