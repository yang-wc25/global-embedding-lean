import GlobalEmbedding.Paper.MatrixSmallResidualNewtonBall
import GlobalEmbedding.Paper.BalancedImplicitLocalSolution

/-!
# Smooth families of quantitative Newton corrections

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
lines 311–315. DAG node: `matrix-smooth-newton-family`.
-/

open Set Metric
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A smooth family of nonlinear equations with a uniform normalized derivative bound and
small residual has a unique smooth family of small zeros. Identical fiber equations give
identical selected zeros.

Proof: choose the unique root in the common ball from the quantitative Newton theorem.
Its strict interior bound and invertible vertical derivative allow the smooth implicit
function theorem at every parameter. The local smooth branch remains inside the common
ball near its base parameter and hence equals the selected roots by uniqueness. This proves
smoothness without initially assuming continuity of the selected roots. Equality of roots
for identical fiber equations follows from the same uniqueness.
Source: `prop:matrix` proof, lines 311–315. -/
theorem smooth_small_residual_newton_family
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (U : Set P) (hU : IsOpen U) (f : P → X → X) (A : P → X ≃L[ℝ] X)
    (r : ℝ) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ univ))
    (hD : ∀ p ∈ U, ∀ x ∈ closedBall (0 : X) r,
      ‖ContinuousLinearMap.id ℝ X - (A p).symm.toContinuousLinearMap.comp
        (fderiv ℝ (f p) x)‖ ≤ 1 / 4)
    (hres : ∀ p ∈ U, ‖(A p).symm (f p 0)‖ ≤ r / 2) :
    ∃ c : P → X, ContDiffOn ℝ ∞ c U ∧
      (∀ p ∈ U, f p (c p) = 0 ∧
        ‖c p‖ ≤ (4 / 3 : ℝ) * ‖(A p).symm (f p 0)‖ ∧ ‖c p‖ ≤ 2 * r / 3 ∧
        (∀ y : X, ‖y‖ ≤ r → f p y = 0 → y = c p)) ∧
      (∀ p ∈ U, ∀ q ∈ U, (∀ x, f p x = f q x) → c p = c q) := by
  have hdiff (p : P) (hp : p ∈ U) (x : X) : DifferentiableAt ℝ (f p) x := by
    have hc : ContDiffAt ℝ ∞ (Function.uncurry f) (p, x) :=
      hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ x⟩)
    exact (hc.differentiableAt (by simp)).comp x (hasFDerivAt_prodMk_right p x).differentiableAt
  have hex (p : P) : ∃ x : X, p ∈ U →
      ‖x‖ ≤ r ∧ f p x = 0 ∧
      ‖x‖ ≤ (4 / 3 : ℝ) * ‖(A p).symm (f p 0)‖ ∧ ‖x‖ ≤ 2 * r / 3 ∧
      (fderiv ℝ (f p) x).IsInvertible ∧
      ∀ y : X, ‖y‖ ≤ r → f p y = 0 → y = x := by
    by_cases hp : p ∈ U
    · obtain ⟨x, hx⟩ := small_residual_newton_ball (f p) (A p) r hr
        (fun x _ ↦ hdiff p hp x) (hD p hp) (hres p hp)
      exact ⟨x, fun _ ↦ hx⟩
    · exact ⟨0, fun h ↦ (hp h).elim⟩
  choose c hc using hex
  have hsmooth : ContDiffOn ℝ ∞ c U := by
    intro p hp
    have hcp := hc p hp
    have hfull : ContDiffAt ℝ ∞ (Function.uncurry f) (p, c p) := hf.contDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ (c p)⟩)
    have hvertical : fderiv ℝ (f p) (c p) =
        (fderiv ℝ (Function.uncurry f) (p, c p)).comp
          (ContinuousLinearMap.inr ℝ P X) := by
      exact (hfull.differentiableAt (by simp)).hasFDerivAt.comp (c p)
        (hasFDerivAt_prodMk_right p (c p)) |>.fderiv
    have hinv : ((fderiv ℝ (Function.uncurry f) (p, c p)).comp
        (ContinuousLinearMap.inr ℝ P X)).IsInvertible := by
      rw [← hvertical]
      exact hcp.2.2.2.2.1
    obtain ⟨V, hV, hpV, hVU, g, hg, hbase, heq⟩ := balanced_implicit_local_solution
      U hU (Function.uncurry f) hf p (c p) hp hcp.2.1 hinv
    have hgAt : ContDiffAt ℝ ∞ g p := hg.contDiffAt (hV.mem_nhds hpV)
    have hgsmall : ∀ᶠ q in 𝓝 p, ‖g q‖ < r := by
      apply hgAt.continuousAt.norm.eventually_lt_const
      change ‖g p‖ < r
      rw [hbase]
      linarith [hcp.2.2.2.1]
    have hsame : g =ᶠ[𝓝 p] c := by
      filter_upwards [hV.mem_nhds hpV, hgsmall] with q hq hqsmall
      exact (hc q (hVU hq)).2.2.2.2.2 (g q) hqsmall.le (heq q hq)
    exact (hgAt.congr_of_eventuallyEq hsame.symm).contDiffWithinAt
  refine ⟨c, hsmooth, ?_, ?_⟩
  · intro p hp
    have h := hc p hp
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩
  · intro p hp q hq heq
    apply (hc q hq).2.2.2.2.2
    · exact (hc p hp).1
    · rw [← heq, (hc p hp).2.1]

#print axioms smooth_small_residual_newton_family

end GlobalEmbedding.Paper
