import GlobalEmbedding.Paper.LittlePeriodicCAlphaDirectionalDerivative
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateContinuous
import GlobalEmbedding.Paper.LittlePeriodicCAlphaComplete
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# An actual Hölder-space integral formula for translation differences

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-translation-fundamental-theorem`.
-/

open MeasureTheory intervalIntegral

namespace GlobalEmbedding.Paper

/-- Translation differences equal the integral of translated directional derivatives in the
actual lower-order little Hölder space, when the high/low representatives have the same lift.

Proof: actual joint continuity makes the derivative orbit norm-integrable in the complete
actual little space. Every actual continuous evaluation commutes with this Bochner integral.
At each lift point the ordinary fundamental theorem of calculus identifies the integral with
the translation difference. Underlying-lift injectivity gives equality in the actual carrier.
No Banach-valued orbit differentiability is assumed. Source: translation in `lem:balanced`. -/
theorem littlePeriodicCAlpha_translate_integral {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N (k + 1) α)
    (g : LittlePeriodicCAlphaFunction a N k α) (hfg : f.val.toFun = g.val.toFun)
    (hα : α ≤ 1) (h : EuclideanSpace ℝ (Fin a)) :
    (∫ t : ℝ in 0..1, littlePeriodicCAlphaTranslateIsometry (t • h)
      (littlePeriodicCAlphaDirectionalDerivative h f)) =
      littlePeriodicCAlphaTranslateIsometry h g - g := by
  let F : ℝ → LittlePeriodicCAlphaFunction a N k α := fun t ↦
    littlePeriodicCAlphaTranslateIsometry (t • h) (littlePeriodicCAlphaDirectionalDerivative h f)
  have hcont : Continuous F :=
    (littlePeriodicCAlpha_translate_joint_continuous hα).comp
      ((continuous_id.smul continuous_const).prodMk continuous_const)
  have hint : IntervalIntegrable F volume 0 1 := hcont.intervalIntegrable 0 1
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  obtain ⟨ev, hev, hnorm⟩ := collar_little_holder_evaluation (N := N) (k := k) (α := α) x
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ ↦ f.val.toFun (x + s • h))
      (fderiv ℝ f.val.toFun (x + t • h) h) t := by
    have hpath : HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const h).const_add x
    exact (f.val.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
      t hpath
  have heval (t : ℝ) : ev (F t) = fderiv ℝ f.val.toFun (x + t • h) h := by
    rw [hev]
    rfl
  have hpointint : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ f.val.toFun (x + t • h) h) volume 0 1 := by
    simpa only [Function.comp_def, heval] using
      (ev.continuous.comp hcont).intervalIntegrable (μ := volume) 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hderiv t) hpointint
  have hsub : (periodicCAlphaTranslate h g.val - g.val).toFun =
      (periodicCAlphaTranslate h g.val).toFun - g.val.toFun :=
    congrArg (fun z : periodicCAlphaSubmodule a N k α ↦ z.val)
      ((periodicCAlphaCarrierEquiv a N k α).addEquiv.map_sub
        (periodicCAlphaTranslate h g.val) g.val)
  calc
    _ = ev (∫ t : ℝ in 0..1, F t) := (hev _).symm
    _ = ∫ t : ℝ in 0..1, fderiv ℝ f.val.toFun (x + t • h) h := by
      rw [← ev.intervalIntegral_comp_comm hint]
      simp only [heval]
    _ = f.val.toFun (x + h) - f.val.toFun x := by
      simpa only [one_smul, zero_smul, add_zero] using hFTC
    _ = _ := by
      change _ = (periodicCAlphaTranslate h g.val - g.val).toFun x
      rw [hsub]
      change f.val.toFun (x + h) - f.val.toFun x = g.val.toFun (x + h) - g.val.toFun x
      rw [hfg]

#print axioms littlePeriodicCAlpha_translate_integral

end GlobalEmbedding.Paper
