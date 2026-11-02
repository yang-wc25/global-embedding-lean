import GlobalEmbedding.Paper.LittlePeriodicCAlphaSourceFamilyDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Genuine norm C∞ of globally source-smooth actual little Hölder families

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-source-family-smooth`.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A globally source-joint-C∞ actual little Hölder family is genuinely C∞ in its original norm.

Prove every finite differentiability order by induction. Order zero is the actual norm
continuity theorem. Construct the actual genuine Fréchet derivative family for the successor.
Applied to each direction it is again a source-joint-C∞ actual family, so induction and the
finite-domain C^n operator criterion prove the derivative has the preceding regularity.
The successor criterion and all-finite-orders criterion give genuine C∞.
Source: smooth parameter slices in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_source_family_smooth
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a N k : ℕ} {α : ℝ} (F : P → LittlePeriodicCAlphaFunction a N k α)
    (hF : ContDiff ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦ (F z.1).val.toFun z.2))
    (hα : α ≤ 1) : ContDiff ℝ ∞ F := by
  rw [contDiff_infty]
  intro n
  induction n generalizing F with
  | zero =>
      apply contDiff_zero.mpr
      apply continuous_induced_rng.mpr
      exact periodicCAlpha_smooth_family_continuous (fun p ↦ (F p).val) hF hα
  | succ n ih =>
      obtain ⟨A, hA, hderiv, hformula⟩ := littlePeriodicCAlpha_source_family_derivative F hF hα
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨A, ?_, hderiv⟩
      apply contDiff_clm_apply_iff.mpr
      intro v
      apply ih
      simp_rw [hformula]
      exact (smooth_parameter_derivative (fun p ↦ (F p).val.toFun) hF).comp
        ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)

#print axioms littlePeriodicCAlpha_source_family_smooth

end GlobalEmbedding.Paper
