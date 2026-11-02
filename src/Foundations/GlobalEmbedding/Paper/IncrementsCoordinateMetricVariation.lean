import GlobalEmbedding.Paper.InducedMetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Actual coordinate first variation of the original induced metric

Source: `main.tex`, lem:increments, lines617–620.
DAG: `increments-coordinate-metric-variation`; W2.
The left side is the literal real derivative of the SAME inducedMetric(F+sZ),
not a formal linearized tensor. Spatial derivatives and Hessians are actual fderiv.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Native differentiation of the actual induced metric of F+sZ in an actual
Euclidean chart. The true first jets are affine in s; native inner differentiation
therefore gives both actual first-variation terms. No immersion or desired
variation identity is supplied. Source: lem:increments617–620. -/
theorem increments_inducedMetric_hasDerivAt {n N : ℕ}
    (F Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v w : EuclideanSpace ℝ (Fin n))
    (hF : DifferentiableAt ℝ F x) (hZ : DifferentiableAt ℝ Z x) :
    HasDerivAt (fun s : ℝ ↦ inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun y ↦ F y + s • Z y) x
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm v)
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm w))
      (inner ℝ (fderiv ℝ F x v) (fderiv ℝ Z x w) +
        inner ℝ (fderiv ℝ Z x v) (fderiv ℝ F x w)) 0 := by
  have hjet (s : ℝ) : fderiv ℝ (fun y ↦ F y + s • Z y) x =
      fderiv ℝ F x + s • fderiv ℝ Z x :=
    (hF.hasFDerivAt.add (hZ.hasFDerivAt.const_smul s)).fderiv
  have heq : (fun s : ℝ ↦ inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun y ↦ F y + s • Z y) x
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm v)
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm w)) =
      fun s ↦ inner ℝ (fderiv ℝ F x v + s • fderiv ℝ Z x v)
        (fderiv ℝ F x w + s • fderiv ℝ Z x w) := by
    funext s
    rw [inducedMetric_apply, mfderiv_eq_fderiv]
    change inner ℝ (fderiv ℝ (fun y ↦ F y + s • Z y) x v)
      (fderiv ℝ (fun y ↦ F y + s • Z y) x w) = _
    simp only [hjet, add_apply, smul_apply]
  have hv := ((hasDerivAt_id (0 : ℝ)).smul_const (fderiv ℝ Z x v)).const_add
    (fderiv ℝ F x v)
  have hw := ((hasDerivAt_id (0 : ℝ)).smul_const (fderiv ℝ Z x w)).const_add
    (fderiv ℝ F x w)
  rw [heq]
  simpa only [zero_smul, add_zero, one_smul, id_eq] using hv.inner ℝ hw

/-- The actual lowered displacement pairing gives the true coordinate
first-variation formula with the actual Hessian. Apply native spatial inner and
CLM evaluation derivatives twice, then the native C2 Hessian symmetry theorem.
This is the geometric derivative identity used before inserting the actual Gram
inverse tangential/normal decomposition; no prescribed derivative cancellation
is assumed. Source: lem:increments617–620. -/
theorem increments_metric_variation_lowered_pairings {n N : ℕ}
    (F Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v w : EuclideanSpace ℝ (Fin n))
    (hF : ContDiffAt ℝ 2 F x) (hZ : DifferentiableAt ℝ Z x) :
    deriv (fun s : ℝ ↦ inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun y ↦ F y + s • Z y) x
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm v)
      ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm w)) 0 =
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ F y w) (Z y)) x v +
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ F y v) (Z y)) x w -
      2 * inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (Z x) := by
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFi (u : EuclideanSpace ℝ (Fin n)) :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ F y u) x :=
    hDF.clm_apply (differentiableAt_const u)
  have hjet (u t : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y ↦ fderiv ℝ F y u) x t = fderiv ℝ (fderiv ℝ F) x t u := by
    rw [fderiv_clm_apply hDF (differentiableAt_const u)]
    simp
  have hi := fderiv_inner_apply ℝ (hFi w) hZ v
  have hj := fderiv_inner_apply ℝ (hFi v) hZ w
  rw [hjet w v] at hi
  rw [hjet v w, hF.isSymmSndFDerivAt (by norm_num) w v] at hj
  have ht := (increments_inducedMetric_hasDerivAt F Z x v w
    (hF.differentiableAt (by norm_num)) hZ).deriv
  have hc := real_inner_comm (fderiv ℝ F x w) (fderiv ℝ Z x v)
  linarith

end GlobalEmbedding.Paper
