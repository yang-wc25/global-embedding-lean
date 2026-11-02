import GlobalEmbedding.Paper.CollarContractionDerivativeBoundary
import GlobalEmbedding.Paper.CollarClosedSubmoduleDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic

/-!
# The real-form derivative of a quadratic contraction on a closed ball

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2), proof lines 530–534. This derives the real linearization bound and preservation
needed for the complex inverse from the actual invariant-ball contraction hypotheses.
-/

open scoped NNReal

namespace GlobalEmbedding.Paper

/-- At any point of a positive-radius real contraction ball, the quadratic complex linearization
preserves the real form and has norm bounded by the contraction constant on that form.

Source: Proposition `prop:collar`, equation (5.2), proof lines 530–534.
Restrict the quadratic map to the real subspace. It is C¹ by the bounded bilinear operations.
Differentiate the complex polynomial explicitly, restrict its derivative to real scalars, and
compose with the real subspace inclusion. This identifies its real derivative with the stated
complex linearization on real vectors. The closed-ball derivative-norm and closed-subspace
preservation theorems then give both conclusions, including at boundary base points.
-/
theorem collar_quadratic_real_ball_linearization
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (f₀ : E) (A : F →L[ℂ] E) (B : E →L[ℂ] E →L[ℂ] F)
    (R : Submodule ℝ E) (hR : IsClosed (R : Set E))
    (x₀ : R) (ρ : ℝ) (hρ : 0 < ρ) (hx₀ : ‖x₀‖ ≤ ρ) (q : ℝ≥0)
    (hmap : Set.MapsTo (fun x : R ↦ f₀ + A (B (x : E) (x : E)))
      (Metric.closedBall 0 ρ) R)
    (hlip : LipschitzOnWith q (fun x : R ↦ f₀ + A (B (x : E) (x : E)))
      (Metric.closedBall 0 ρ)) :
    let T := A.comp (B (x₀ : E) + B.flip (x₀ : E))
    (∀ x : E, x ∈ R → T x ∈ R) ∧
      (∀ x : E, x ∈ R → ‖T x‖ ≤ (q : ℝ) * ‖x‖) := by
  let T := A.comp (B (x₀ : E) + B.flip (x₀ : E))
  let H : R → E := fun x ↦ f₀ + A (B (x : E) (x : E))
  have hsub : ContDiff ℝ 1 (fun x : R ↦ (x : E)) := R.subtypeL.contDiff
  have hQ : ContDiff ℝ 1 (fun x : R ↦ B (x : E) (x : E)) := by
    exact (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp
      (hsub.prodMk hsub)
  have hH : ContDiff ℝ 1 H :=
    contDiff_const.add ((A.restrictScalars ℝ).contDiff.comp hQ)
  have hB : HasFDerivAt (fun x : E ↦ B x x)
      (B (x₀ : E) + B.flip (x₀ : E)) (x₀ : E) := by
    have heq : B.precompR E (x₀ : E) (ContinuousLinearMap.id ℂ E) +
        B.precompL E (ContinuousLinearMap.id ℂ E) (x₀ : E) =
          B (x₀ : E) + B.flip (x₀ : E) := by
      ext v
      simp
    simpa only [id_eq, heq] using
      B.hasFDerivAt_of_bilinear (hasFDerivAt_id (x₀ : E)) (hasFDerivAt_id (x₀ : E))
  have hcomplex : HasFDerivAt (fun x : E ↦ f₀ + A (B x x)) T (x₀ : E) :=
    (A.hasFDerivAt.comp (x₀ : E) hB).const_add f₀
  have hreal : HasFDerivAt H ((T.restrictScalars ℝ).comp R.subtypeL) x₀ :=
    (hcomplex.restrictScalars ℝ).comp x₀ R.subtypeL.hasFDerivAt
  have hD : fderiv ℝ H x₀ = (T.restrictScalars ℝ).comp R.subtypeL := hreal.fderiv
  have hx : x₀ ∈ Metric.closedBall (0 : R) ρ := by
    simpa only [mem_closedBall_zero_iff] using hx₀
  have hnorm := collar_contraction_derivative_boundary H hH 0 ρ hρ q hlip x₀ hx
  have hpres := collar_closed_submodule_derivative H hH R hR 0 ρ hρ hmap x₀ hx
  constructor
  · intro x hxR
    have hm := hpres (⟨x, hxR⟩ : R)
    rw [hD] at hm
    exact hm
  · intro x hxR
    calc
      ‖T x‖ = ‖fderiv ℝ H x₀ (⟨x, hxR⟩ : R)‖ := by rw [hD]; rfl
      _ ≤ ‖fderiv ℝ H x₀‖ * ‖(⟨x, hxR⟩ : R)‖ :=
        (fderiv ℝ H x₀).le_opNorm _
      _ ≤ (q : ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_quadratic_real_ball_linearization
