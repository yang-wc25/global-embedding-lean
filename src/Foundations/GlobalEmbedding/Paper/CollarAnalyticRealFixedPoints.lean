import GlobalEmbedding.Paper.CollarAnalyticRealFixedFamily

/-!
# Analytic dependence of the real quadratic contraction fixed points

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2), proof lines 524–534. This constructs the actual real fixed points from the
invariant-ball hypotheses, including a radius-zero ball, before proving their analytic extension.
-/

open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Analytic coefficient expansions and a common invariant real contraction ball give a local
complex analytic map whose real restriction is the unique fixed point in that ball.

Source: Proposition `prop:collar`, equation (5.2), proof lines 524–534.
The real ball is closed in the complete ambient space, hence complete, and contains zero because
its radius is nonnegative. For each nearby parameter, restrict the invariant map to that ball
and apply Mathlib's complete-subset contraction theorem to obtain a fixed point there. Choose
these fixed points, using zero away from the parameter neighborhood. The analytic real-family
extension theorem applies to this actual family and gives an analytic map agreeing with it for
nearby real parameters. Its real values therefore belong to the ball and solve the equation.
If any other ball point solves the same equation, the contraction estimate gives
`dist(x,y) ≤ q*dist(x,y)`, which forces equality because `q<1`. Thus the real restriction
is precisely the unique fixed point. No continuity, derivative bounds, interior-ball margin or
preexisting fixed-point family is added as an assumption.
-/
theorem collar_analytic_real_fixed_points
    {Z E F : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℂ Z]
    [IsScalarTower ℝ ℂ Z] [CompleteSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (P : Submodule ℝ Z) (R : Submodule ℝ E) (hR : IsClosed (R : Set E))
    (r s : E →L[ℝ] R)
    (hdecomp : ∀ x : E, (r x : E) + Complex.I • (s x : E) = x)
    (f : Z → E) (A : Z → F →L[ℂ] E) (B : E →L[ℂ] E →L[ℂ] F)
    (p₀ : P) (ρ : ℝ) (hρ : 0 ≤ ρ) (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hf : AnalyticAt ℂ f (p₀ : Z)) (hA : AnalyticAt ℂ A (p₀ : Z))
    (hnear : ∀ᶠ p : P in 𝓝 p₀,
      let S : Set E := {x | x ∈ R ∧ ‖x‖ ≤ ρ}
      let Φ : E → E := fun x ↦ f (p : Z) + A (p : Z) (B x x)
      Set.MapsTo Φ S S ∧ LipschitzOnWith q Φ S) :
    ∃ ψ : Z → E, AnalyticAt ℂ ψ (p₀ : Z) ∧
      ∀ᶠ p : P in 𝓝 p₀,
        let S : Set E := {x | x ∈ R ∧ ‖x‖ ≤ ρ}
        let Φ : E → E := fun x ↦ f (p : Z) + A (p : Z) (B x x)
        ψ (p : Z) ∈ S ∧ Φ (ψ (p : Z)) = ψ (p : Z) ∧
          ∀ x ∈ S, Φ x = x ↔ ψ (p : Z) = x := by
  classical
  let S : Set E := {x | x ∈ R ∧ ‖x‖ ≤ ρ}
  let Φ : Z → E → E := fun z x ↦ f z + A z (B x x)
  let good : P → Prop := fun p ↦ Set.MapsTo (Φ (p : Z)) S S ∧
    LipschitzOnWith q (Φ (p : Z)) S
  change ∀ᶠ p : P in 𝓝 p₀, good p at hnear
  have hclosed : IsClosed S := hR.inter (isClosed_le continuous_norm continuous_const)
  have hzero : (0 : E) ∈ S := ⟨R.zero_mem, by simpa only [norm_zero] using hρ⟩
  have hex (p : P) (hp : good p) :
      ∃ x : R, (x : E) ∈ S ∧ Φ (p : Z) (x : E) = (x : E) := by
    have hcontract : ContractingWith q (hp.1.restrict (Φ (p : Z)) S S) := by
      refine ⟨hq, LipschitzWith.of_dist_le_mul ?_⟩
      intro x y
      exact hp.2.dist_le_mul (x : E) x.property (y : E) y.property
    obtain ⟨x, hx, hfixed, hconv, hbound⟩ :=
      ContractingWith.exists_fixedPoint' hclosed.isComplete hp.1 hcontract hzero
        (edist_ne_top _ _)
    exact ⟨⟨x, hx.1⟩, hx, hfixed.eq⟩
  let g : P → R := fun p ↦ if hp : good p then Classical.choose (hex p hp) else 0
  have hgnear : ∀ᶠ p : P in 𝓝 p₀,
      Set.MapsTo (Φ (p : Z)) S S ∧ LipschitzOnWith q (Φ (p : Z)) S ∧
        (g p : E) ∈ S ∧ Φ (p : Z) (g p : E) = (g p : E) := by
    filter_upwards [hnear] with p hp
    have hprops : (g p : E) ∈ S ∧ Φ (p : Z) (g p : E) = (g p : E) := by
      simpa only [g, dite_eq_left hp] using Classical.choose_spec (hex p hp)
    exact ⟨hp.1, hp.2, hprops⟩
  obtain ⟨ψ, hψ, hbase, hagree⟩ := collar_analytic_real_fixed_family
    P R hR r s hdecomp f A B g p₀ ρ q hq hf hA hgnear
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hgnear, hagree] with p hp hag
  have hmemψ : ψ (p : Z) ∈ S := by rw [hag]; exact hp.2.2.1
  have hfixψ : Φ (p : Z) (ψ (p : Z)) = ψ (p : Z) := by rw [hag]; exact hp.2.2.2
  refine ⟨hmemψ, hfixψ, ?_⟩
  intro x hx
  constructor
  · intro hfixx
    change Φ (p : Z) x = x at hfixx
    have hd := hp.2.1.dist_le_mul (ψ (p : Z)) hmemψ x hx
    rw [hfixψ, hfixx] at hd
    have hmul : (1 - (q : ℝ)) * dist (ψ (p : Z)) x ≤ 0 := by nlinarith [hd]
    have hdist₀ : dist (ψ (p : Z)) x ≤ 0 := by
      apply (mul_le_mul_iff_right₀ (sub_pos.mpr hq)).mp
      simpa only [mul_zero] using hmul
    exact dist_le_zero.mp hdist₀
  · intro heq
    rw [← heq]
    exact hfixψ

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_analytic_real_fixed_points
