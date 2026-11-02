import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint source smoothness of actual parameter directional derivatives

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-smooth-parameter-derivative`.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Joint genuine source smoothness persists after parameter differentiation and evaluation
in a varying parameter direction.

Apply parameterized partial-fderiv smoothness to F(q,x) at q=p, then evaluate the resulting
continuous linear map on v. Source: mixed source derivatives in `lem:balanced`. -/
theorem smooth_parameter_derivative
    {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : P → X → Y) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun z : (P × P) × X ↦ fderiv ℝ (fun q ↦ F q z.2) z.1.1 z.1.2) := by
  have hd : ContDiff ℝ ∞ (fun z : P × X ↦ fderiv ℝ (fun q ↦ F q z.2) z.1) :=
    (hF.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv contDiff_fst (by simp)
  exact (hd.comp (contDiff_fst.fst.prodMk contDiff_snd)).clm_apply contDiff_fst.snd

#print axioms smooth_parameter_derivative

end GlobalEmbedding.Paper
