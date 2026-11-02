import GlobalEmbedding.Paper.CollarAnalyticImplicit
import GlobalEmbedding.Paper.CollarQuadraticAnalyticEquation
import GlobalEmbedding.Paper.CollarRealContractionComplexInverse

/-!
# The analytic branch of the collar quadratic equation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2), proof lines 530–534. This combines analytic coefficient expansions with the
real-form inverse bound, without assuming the complex operator norm is less than one or using
a general theorem converting arbitrary Banach-domain holomorphy to analyticity.
-/

open scoped Topology

namespace GlobalEmbedding.Paper

/-- Analytic coefficients and a real-contracting vertical linearization give the local analytic
branch of the collar quadratic fixed-point equation, with its base value and local uniqueness.

Source: Proposition `prop:collar`, equation (5.2), proof lines 530–534.
The residual `G(z,x)=x-f(z)-A(z)B(x,x)` is analytic by the quadratic analytic-equation theorem.
Its vertical derivative is `I-T`, where `T=A(z₀)∘(B(x₀,·)+B(·,x₀))`. The real-form contraction
bound gives a convergent complex Neumann inverse for `I-T`, including for norms for which
`‖T‖` is not less than one. The analytic Banach implicit-function theorem then supplies the
branch, base value, equation and local uniqueness. This theorem isolates the analytic branch
construction; the closed-ball derivative estimates and continuity of existing real fixed points
are separate prerequisites for applying it to the original invariant-ball family.
-/
theorem collar_quadratic_analytic_branch
    {Z E F : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : Z → E) (A : Z → F →L[ℂ] E) (B : E →L[ℂ] E →L[ℂ] F)
    (z₀ : Z) (x₀ : E) (hf : AnalyticAt ℂ f z₀) (hA : AnalyticAt ℂ A z₀)
    (hfixed : f z₀ + A z₀ (B x₀ x₀) = x₀)
    (R : Submodule ℝ E) (r s : E →L[ℝ] R)
    (hdecomp : ∀ x : E, (r x : E) + Complex.I • (s x : E) = x)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hpres : ∀ x : E, x ∈ R → (A z₀).comp (B x₀ + B.flip x₀) x ∈ R)
    (hcontract : ∀ x : E, x ∈ R →
      ‖(A z₀).comp (B x₀ + B.flip x₀) x‖ ≤ q * ‖x‖) :
    ∃ ψ : Z → E, AnalyticAt ℂ ψ z₀ ∧ ψ z₀ = x₀ ∧
      (∀ᶠ z in 𝓝 z₀, f z + A z (B (ψ z) (ψ z)) = ψ z) ∧
      (∀ᶠ p in 𝓝 (z₀, x₀), f p.1 + A p.1 (B p.2 p.2) = p.2 ↔ ψ p.1 = p.2) := by
  let G : Z × E → E := fun p ↦ p.2 - f p.1 - A p.1 (B p.2 p.2)
  obtain ⟨hG, hD⟩ := collar_quadratic_analytic_equation f A B z₀ x₀ hf hA
  have hzero : G (z₀, x₀) = 0 := by
    dsimp [G]
    rw [sub_sub, hfixed, sub_self]
  obtain ⟨K, hK, hbound, hsum, hInv, hHasSum⟩ :=
    collar_real_contraction_complex_inverse R r s hdecomp
      ((A z₀).comp (B x₀ + B.flip x₀)) q hq₀ hq₁ hpres hcontract
  have hvertical : (fderiv ℂ G (z₀, x₀) ∘L ContinuousLinearMap.inr ℂ Z E).IsInvertible := by
    rw [hD]
    exact hInv
  obtain ⟨ψ, hψ, hbase, heq, huniq⟩ :=
    collar_analytic_banach_implicit G z₀ x₀ hG hzero hvertical
  refine ⟨ψ, hψ, hbase, ?_, ?_⟩
  · filter_upwards [heq] with z hz
    exact (sub_eq_zero.mp (show ψ z - (f z + A z (B (ψ z) (ψ z))) = 0 by
      simpa only [G, sub_sub] using hz)).symm
  · filter_upwards [huniq] with p hp
    have hres : G p = 0 ↔ f p.1 + A p.1 (B p.2 p.2) = p.2 := by
      dsimp only [G]
      rw [sub_sub, sub_eq_zero]
      exact eq_comm
    exact hres.symm.trans hp

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_quadratic_analytic_branch
