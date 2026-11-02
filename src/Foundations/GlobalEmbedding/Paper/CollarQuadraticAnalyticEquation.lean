import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Complex.Basic

/-!
# The analytic residual and vertical derivative of the collar quadratic equation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2) and proof lines 530–534. Once the translated coefficients have analytic
Banach-valued expansions, the residual is analytic in both the parameter and the unknown.
Its vertical derivative is expressed without assuming symmetry of the bilinear operator.
-/

namespace GlobalEmbedding.Paper

/-- Analytic coefficient expansions give an analytic collar residual with the expected vertical
linearization. Source: Proposition `prop:collar`, equation (5.2), proof lines 530–534.

Compose the analytic bilinear maps with the coordinate projections and the coefficient expansions
to obtain analyticity. The bilinear product rule gives the derivative of `B(x,x)` as the sum
`B(x₀,·)+B(·,x₀)`. Composing with the fixed linear coefficient and subtracting from the identity
computes the derivative of the residual with the parameter fixed. Uniqueness of the Fréchet
derivative identifies it with the derivative of the joint residual restricted to the second factor.
-/
theorem collar_quadratic_analytic_equation
    {Z E F : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : Z → E) (A : Z → F →L[ℂ] E) (B : E →L[ℂ] E →L[ℂ] F)
    (z₀ : Z) (x₀ : E) (hf : AnalyticAt ℂ f z₀) (hA : AnalyticAt ℂ A z₀) :
    let G : Z × E → E := fun p ↦ p.2 - f p.1 - A p.1 (B p.2 p.2)
    AnalyticAt ℂ G (z₀, x₀) ∧
      fderiv ℂ G (z₀, x₀) ∘L ContinuousLinearMap.inr ℂ Z E =
        ContinuousLinearMap.id ℂ E - (A z₀).comp (B x₀ + B.flip x₀) := by
  dsimp only
  let G : Z × E → E := fun p ↦ p.2 - f p.1 - A p.1 (B p.2 p.2)
  have hQ : AnalyticAt ℂ (fun p : Z × E ↦ B p.2 p.2) (z₀, x₀) := by
    exact AnalyticAt.comp
      (g := fun v : E × E ↦ B v.1 v.2)
      (f := fun p : Z × E ↦ (p.2, p.2))
      (B.analyticAt_bilinear (x₀, x₀))
      ((analyticAt_snd : AnalyticAt ℂ (Prod.snd : Z × E → E) (z₀, x₀)).prod
        analyticAt_snd)
  have hG : AnalyticAt ℂ G (z₀, x₀) :=
    (analyticAt_snd.sub (hf.comp analyticAt_fst)).sub
      (((ContinuousLinearMap.apply ℂ E).analyticAt_bilinear (B x₀ x₀, A z₀)).comp₂ hQ
        (hA.comp analyticAt_fst))
  have hB : HasFDerivAt (fun x ↦ B x x) (B x₀ + B.flip x₀) x₀ := by
    have heq : B.precompR E x₀ (ContinuousLinearMap.id ℂ E) +
        B.precompL E (ContinuousLinearMap.id ℂ E) x₀ = B x₀ + B.flip x₀ := by
      ext v
      simp
    simpa only [id_eq, heq] using
      B.hasFDerivAt_of_bilinear (hasFDerivAt_id x₀) (hasFDerivAt_id x₀)
  have hx : HasFDerivAt (fun x ↦ G (z₀, x))
      (ContinuousLinearMap.id ℂ E - (A z₀).comp (B x₀ + B.flip x₀)) x₀ :=
    ((hasFDerivAt_id x₀).sub_const (f z₀)).sub ((A z₀).hasFDerivAt.comp x₀ hB)
  have hjoint := hG.differentiableAt.hasFDerivAt.comp x₀ (hasFDerivAt_prodMk_right z₀ x₀)
  exact ⟨hG, hjoint.unique hx⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_quadratic_analytic_equation
