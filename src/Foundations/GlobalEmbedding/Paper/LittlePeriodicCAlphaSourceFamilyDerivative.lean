import GlobalEmbedding.Paper.LittlePeriodicCAlphaParameterDerivativeData
import GlobalEmbedding.Paper.LittlePeriodicCAlphaPointwiseC1

/-!
# Genuine norm Fréchet derivatives of globally source-smooth actual Hölder families

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-source-family-frechet-derivative`.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Joint source smoothness yields actual continuous parameter Fréchet derivatives in the
original little Hölder norm, with the exact pointwise source derivative formula.

Construct the actual derivative operators and their norm continuity. Ordinary source line
calculus gives the pointwise derivatives, so the Bochner norm-C¹ bridge proves genuine norm
C¹. Composing its genuine derivative with actual continuous evaluations identifies it with
the constructed candidate by pointwise derivative uniqueness and actual lift injectivity.
Source: smooth parameter slices in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_source_family_derivative
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a N k : ℕ} {α : ℝ} (F : P → LittlePeriodicCAlphaFunction a N k α)
    (hF : ContDiff ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦ (F z.1).val.toFun z.2))
    (hα : α ≤ 1) :
    ∃ A : P → P →L[ℝ] LittlePeriodicCAlphaFunction a N k α,
      Continuous A ∧ (∀ p, HasFDerivAt F (A p) p) ∧
      ∀ (p v : P) (x : EuclideanSpace ℝ (Fin a)),
        (A p v).val.toFun x = fderiv ℝ (fun q ↦ (F q).val.toFun x) p v := by
  obtain ⟨A, hA, hformula⟩ := littlePeriodicCAlpha_parameter_derivative_data F hF hα
  have hxsource (x : EuclideanSpace ℝ (Fin a)) :
      ContDiff ℝ ∞ (fun q : P ↦ (F q).val.toFun x) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hc1 : ContDiff ℝ 1 F := by
    apply littlePeriodicCAlpha_contDiff_one_of_pointwise F A hA
    intro p v x t
    rw [hformula]
    have hpath : HasDerivAt (fun s : ℝ ↦ p + s • v) v t := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add p
    exact ((hxsource x).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
      t hpath
  refine ⟨A, hA, ?_, hformula⟩
  intro p
  have hactual := (hc1.differentiable (by norm_num)).differentiableAt.hasFDerivAt (x := p)
  have heq : fderiv ℝ F p = A p := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    obtain ⟨ev, hev, hnorm⟩ := collar_little_holder_evaluation (N := N) (k := k) (α := α) x
    have heval := ev.hasFDerivAt.comp p hactual
    have hfun : (fun q ↦ ev (F q)) = (fun q ↦ (F q).val.toFun x) := funext (fun q ↦ hev _)
    change HasFDerivAt (fun q ↦ ev (F q)) (ev.comp (fderiv ℝ F p)) p at heval
    rw [hfun] at heval
    have hpoint := ((hxsource x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := p)
    have hunique := congrArg (fun B : P →L[ℝ] EuclideanSpace ℝ (Fin N) ↦ B v)
      (heval.unique hpoint)
    calc
      _ = ev ((fderiv ℝ F p) v) := (hev _).symm
      _ = fderiv ℝ (fun q ↦ (F q).val.toFun x) p v := hunique
      _ = _ := (hformula p v x).symm
  rw [← heq]
  exact hactual

#print axioms littlePeriodicCAlpha_source_family_derivative

end GlobalEmbedding.Paper
