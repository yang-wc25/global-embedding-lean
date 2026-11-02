import GlobalEmbedding.Paper.CollarFixedPointContinuity
import GlobalEmbedding.Paper.CollarQuadraticAnalyticBranch
import GlobalEmbedding.Paper.CollarQuadraticRealBallLinearization

/-!
# Analytic extension of the collar's real fixed-point family

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2), proof lines 530–534. This combines the coefficient power-series input,
invariant real contraction ball, boundary derivative estimates, complex Neumann inverse,
analytic implicit branch, and continuity needed to identify the real family with that branch.
-/

open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- The real fixed points of the quadratic collar equation on a common invariant contraction ball
admit a local complex analytic extension, given analytic expansions of the coefficients.

Source: Proposition `prop:collar`, equation (5.2), proof lines 530–534.
A radius-zero ball forces the existing real family to be zero, giving the constant analytic
extension. For positive radius, apply the quadratic real-ball linearization theorem at the base
fixed point, including its boundary case. Continuous real-form coordinates yield a complex
Neumann inverse, and the quadratic analytic branch theorem provides a nearby analytic solution
and local uniqueness. The uniform contraction estimate proves continuity of the given real
fixed-point family from continuity of the base-point evaluation. Its graph therefore stays in the
implicit uniqueness neighborhood, where it agrees with the analytic branch. Existence of the real
fixed-point family is supplied separately by the complete closed-ball fixed-point theorem.
The parameter real subspace need not itself be given continuous real-form coordinates, and
no finite-dimensionality is needed once the coefficient expansions are provided.
-/
theorem collar_analytic_real_fixed_family
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
    (g : P → R) (p₀ : P) (ρ : ℝ) (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hf : AnalyticAt ℂ f (p₀ : Z)) (hA : AnalyticAt ℂ A (p₀ : Z))
    (hnear : ∀ᶠ p : P in 𝓝 p₀,
      let S : Set E := {x | x ∈ R ∧ ‖x‖ ≤ ρ}
      let Φ : E → E := fun x ↦ f (p : Z) + A (p : Z) (B x x)
      Set.MapsTo Φ S S ∧ LipschitzOnWith q Φ S ∧
        (g p : E) ∈ S ∧ Φ (g p : E) = (g p : E)) :
    ∃ ψ : Z → E, AnalyticAt ℂ ψ (p₀ : Z) ∧ ψ (p₀ : Z) = (g p₀ : E) ∧
      (∀ᶠ p : P in 𝓝 p₀, ψ (p : Z) = (g p : E)) := by
  let S : Set E := {x | x ∈ R ∧ ‖x‖ ≤ ρ}
  let Φ : Z → E → E := fun z x ↦ f z + A z (B x x)
  change ∀ᶠ p : P in 𝓝 p₀, Set.MapsTo (Φ (p : Z)) S S ∧
    LipschitzOnWith q (Φ (p : Z)) S ∧ (g p : E) ∈ S ∧
      Φ (p : Z) (g p : E) = (g p : E) at hnear
  have h₀ := hnear.self_of_nhds
  have hx₀ : ‖g p₀‖ ≤ ρ := h₀.2.2.1.2
  have hρ₀ : 0 ≤ ρ := (norm_nonneg (g p₀)).trans hx₀
  by_cases hρ : ρ = 0
  · have hz₀ : (g p₀ : E) = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hρ, Submodule.norm_coe] using hx₀) (norm_nonneg _)
    refine ⟨fun _ ↦ 0, analyticAt_const, hz₀.symm, ?_⟩
    filter_upwards [hnear] with p hp
    symm
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [hρ] using hp.2.2.1.2) (norm_nonneg _)
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ₀ (Ne.symm hρ)
  have hmapR : Set.MapsTo
      (fun x : R ↦ f (p₀ : Z) + A (p₀ : Z) (B (x : E) (x : E)))
      (Metric.closedBall (0 : R) ρ) R := by
    intro x hx
    have hxS : (x : E) ∈ S := ⟨x.property, by
      simpa only [mem_closedBall_zero_iff, Submodule.norm_coe] using hx⟩
    exact (h₀.1 hxS).1
  have hlipR : LipschitzOnWith q
      (fun x : R ↦ f (p₀ : Z) + A (p₀ : Z) (B (x : E) (x : E)))
      (Metric.closedBall (0 : R) ρ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxS : (x : E) ∈ S := ⟨x.property, by
      simpa only [mem_closedBall_zero_iff, Submodule.norm_coe] using hx⟩
    have hyS : (y : E) ∈ S := ⟨y.property, by
      simpa only [mem_closedBall_zero_iff, Submodule.norm_coe] using hy⟩
    exact h₀.2.1.dist_le_mul (x : E) hxS (y : E) hyS
  obtain ⟨hpres, hcontract⟩ := collar_quadratic_real_ball_linearization
    (f (p₀ : Z)) (A (p₀ : Z)) B R hR (g p₀) ρ hρpos hx₀ q hmapR hlipR
  obtain ⟨ψ, hψ, hbase, heq, huniq⟩ := collar_quadratic_analytic_branch
    f A B (p₀ : Z) (g p₀ : E) hf hA h₀.2.2.2 R r s hdecomp
      q q.coe_nonneg hq hpres hcontract
  have hinc : ContinuousAt (fun p : P ↦ (p : Z)) p₀ := P.subtypeL.continuous.continuousAt
  have heval : ContinuousAt (fun p : P ↦ Φ (p : Z) (g p₀ : E)) p₀ :=
    (hf.continuousAt.comp hinc).add
      ((hA.continuousAt.comp hinc).clm_apply continuousAt_const)
  have hgcont : ContinuousAt (fun p : P ↦ (g p : E)) p₀ := by
    apply collar_fixed_point_continuity
      (fun p : P ↦ Φ (p : Z)) (fun p : P ↦ (g p : E)) p₀ S q hq
      h₀.2.2.1 h₀.2.2.2 _ heval
    exact hnear.mono fun p hp ↦ ⟨hp.2.2.1, hp.2.2.2, hp.2.1⟩
  have hgraph : ContinuousAt (fun p : P ↦ ((p : Z), (g p : E))) p₀ :=
    hinc.prodMk hgcont
  have huniqr : ∀ᶠ p : P in 𝓝 p₀,
      Φ (p : Z) (g p : E) = (g p : E) ↔ ψ (p : Z) = (g p : E) :=
    hgraph.eventually huniq
  refine ⟨ψ, hψ, hbase, ?_⟩
  filter_upwards [hnear, huniqr] with p hp hu
  exact hu.mp hp.2.2.2

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_analytic_real_fixed_family
