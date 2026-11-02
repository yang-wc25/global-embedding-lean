import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint smoothness of all spatial jets of a genuinely smooth parameter family

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-smooth-spatial-jets`.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Joint genuine C∞ regularity of F(p,x) gives joint genuine C∞ regularity of every spatial jet.

Proof: the zeroth jet is the value transported by the zero-tensor isometry. For the successor,
apply the parameterized partial-fderiv smoothness theorem to the preceding spatial jet, then
uncurry the resulting tensor by the continuous multilinear curry-left equivalence.
Source: mixed parameter/spatial derivatives in the proof of `lem:balanced`. -/
theorem smooth_spatial_jets
    {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : P → X → Y) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun z : P × X ↦ iteratedFDeriv ℝ j (F z.1) z.2) := by
  induction j with
  | zero =>
      exact hF.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ X Y).symm : Y →L[ℝ] X [×0]→L[ℝ] Y)
  | succ j ih =>
      have hH : ContDiff ℝ ∞ (fun z : (P × X) × X ↦
          iteratedFDeriv ℝ j (F z.1.1) z.2) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞ (fun z : P × X ↦ fderiv ℝ
          (iteratedFDeriv ℝ j (F z.1)) z.2) :=
        hH.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) Y).symm :
            (X →L[ℝ] X [×j]→L[ℝ] Y) →L[ℝ] X [×(j + 1)]→L[ℝ] Y)

#print axioms smooth_spatial_jets

end GlobalEmbedding.Paper
