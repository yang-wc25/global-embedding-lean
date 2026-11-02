import Mathlib.Analysis.Calculus.ImplicitContDiff
import GlobalEmbedding.Paper.BalancedImplicitLocalSolution
import GlobalEmbedding.Paper.BalancedImplicitNeumann
import GlobalEmbedding.Paper.BalancedFixedSmallUnique
import GlobalEmbedding.Paper.BalancedFixedEquationVerticalDerivative
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth branches of quadratic fixed points

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:balanced`,
proof, lines 417–425; DAG node `balanced-fixed-implicit-branch`.
-/

open Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A family of solutions to a smooth symmetric quadratic fixed-point equation is smooth when
its linearized quadratic term has norm strictly below one. It is unique among solutions with
that same strict bound.

Proof: At any fixed parameter, the difference of two such solutions equals the sum of the
operators `A (Q v)` and `A (Q w)` applied to their difference. Each operator has norm less than
`1 / 2`, so the solutions agree. The equation map
`G(p,x) = x - f(p) - A(p)(Q(x,x))` is smooth, with x-derivative
`I - 2 A(p) (Q(v(p)))`. The Neumann series makes this derivative invertible. The Banach
implicit-function theorem provides a smooth local solution through each point; continuity of
the local solution and coefficients preserves the strict bound on a smaller neighborhood.
Uniqueness identifies it there with the given family, without assuming the family is
continuous. These local identifications show that the family is smooth on the open parameter
set. Source: Lemma `lem:balanced`, proof, lines 417–425. -/
theorem balanced_fixed_implicit_branch
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (P : Set E) (hP : IsOpen P) (Q : X →L[ℝ] X →L[ℝ] Y)
    (hQ : ∀ x y, Q x y = Q y x)
    (f : E → X) (A : E → Y →L[ℝ] X) (v : E → X)
    (hf : ContDiffOn ℝ ∞ f P) (hA : ContDiffOn ℝ ∞ A P)
    (hfixed : ∀ p ∈ P, v p = f p + A p (Q (v p) (v p)))
    (hsmall : ∀ p ∈ P, ‖(2 : ℝ) • (A p).comp (Q (v p))‖ < 1) :
    ContDiffOn ℝ ∞ v P ∧
      ∀ p ∈ P, ∀ w : X, w = f p + A p (Q w w) →
        ‖(2 : ℝ) • (A p).comp (Q w)‖ < 1 → w = v p := by
  have hunique : ∀ p ∈ P, ∀ w : X, w = f p + A p (Q w w) →
      ‖(2 : ℝ) • (A p).comp (Q w)‖ < 1 → w = v p := by
    intro p hp w hw hs
    exact balanced_fixed_small_unique Q hQ (A p) (f p) w (v p)
      hw (hfixed p hp) hs (hsmall p hp)
  refine ⟨?_, hunique⟩
  let G : E × X → X := fun z ↦ z.2 - f z.1 - A z.1 (Q z.2 z.2)
  have hGP : ContDiffOn ℝ ∞ G (P ×ˢ univ) := by
    apply (hP.prod isOpen_univ).contDiffOn_iff.mpr
    intro z hz
    have hfp : ContDiffAt ℝ ∞ f z.1 := hf.contDiffAt (hP.mem_nhds hz.1)
    have hAp : ContDiffAt ℝ ∞ A z.1 := hA.contDiffAt (hP.mem_nhds hz.1)
    dsimp [G]
    fun_prop
  apply hP.contDiffOn_iff.mpr
  intro p hp
  have hc : ContDiffAt ℝ ∞ G (p, v p) :=
    hGP.contDiffAt ((hP.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
  have hins : HasFDerivAt (fun x : X ↦ (p, x))
      (ContinuousLinearMap.inr ℝ E X) (v p) := by
    convert (hasFDerivAt_const p (v p)).prodMk (hasFDerivAt_id (v p)) using 1 <;>
      rfl
  have hpart : (fderiv ℝ G (p, v p) ∘L ContinuousLinearMap.inr ℝ E X) =
      ContinuousLinearMap.id ℝ X - (2 : ℝ) • (A p).comp (Q (v p)) :=
    ((hc.differentiableAt (by simp)).hasFDerivAt.comp (v p) hins).unique
      (balanced_fixed_equation_hasFDerivAt Q hQ (A p) (f p) (v p))
  have hi : (fderiv ℝ G (p, v p) ∘L ContinuousLinearMap.inr ℝ E X).IsInvertible := by
    rw [hpart]
    exact (balanced_implicit_neumann _ (hsmall p hp)).1
  have hz : G (p, v p) = 0 := by
    change v p - f p - A p (Q (v p) (v p)) = 0
    calc
      v p - f p - A p (Q (v p) (v p)) =
          (f p + A p (Q (v p) (v p))) - f p - A p (Q (v p) (v p)) := by
        rw [← hfixed p hp]
      _ = 0 := by abel
  obtain ⟨U, hU, hpU, hUP, g, hg, hgp, hgzero⟩ :=
    balanced_implicit_local_solution P hP G hGP p (v p) hp hz hi
  have hcg : ContinuousAt g p := (hg.contDiffAt (hU.mem_nhds hpU)).continuousAt
  have hAg : ContinuousAt (fun q ↦ (2 : ℝ) • (A q).comp (Q (g q))) p :=
    ((hA.contDiffAt (hP.mem_nhds hp)).continuousAt.clm_comp
      (Q.continuous.continuousAt.comp (f := g) hcg)).const_smul (2 : ℝ)
  have hsg : ‖(2 : ℝ) • (A p).comp (Q (g p))‖ < 1 := by
    simpa only [hgp] using hsmall p hp
  have hsgnear : ∀ᶠ q in 𝓝 p, ‖(2 : ℝ) • (A q).comp (Q (g q))‖ < 1 :=
    hAg.norm.eventually (gt_mem_nhds hsg)
  apply (hg.contDiffAt (hU.mem_nhds hpU)).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hpU, hsgnear] with q hqU hqs
  apply (hunique q (hUP hqU) (g q) ?_ hqs).symm
  apply sub_eq_zero.mp
  simpa only [G, sub_add_eq_sub_sub] using hgzero q hqU

#print axioms balanced_fixed_implicit_branch

end GlobalEmbedding.Paper
