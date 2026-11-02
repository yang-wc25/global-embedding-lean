import GlobalEmbedding.Paper.BalancedImplicitRecenter

/-!
# Smooth local zero branches

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 418–425; implicit-function expansion. DAG node: `balanced-implicit-local-solution`.
-/

open Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A smooth equation with invertible vertical derivative at a zero has a smooth zero branch
on an open neighborhood of its base parameter.

Proof: the implicit function theorem gives a branch, its value, and equation near the base.
Its C-infinity regularity at the base gives C-one regularity and hence continuity on some
neighborhood. Continuity of the derivative and openness of invertibility give invertible
vertical derivatives along the branch after shrinking. The recentering theorem proves the
branch smooth throughout that neighborhood. Source: `lem:balanced`, lines 418–425. -/
theorem balanced_implicit_local_solution
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : Set E) (hP : IsOpen P) (G : E × X → X)
    (hG : ContDiffOn ℝ ∞ G (P ×ˢ univ))
    (p₀ : E) (x₀ : X) (hp₀ : p₀ ∈ P) (hzero : G (p₀, x₀) = 0)
    (hinv : (fderiv ℝ G (p₀, x₀) ∘L ContinuousLinearMap.inr ℝ E X).IsInvertible) :
    ∃ U : Set E, IsOpen U ∧ p₀ ∈ U ∧ U ⊆ P ∧
      ∃ g : E → X, ContDiffOn ℝ ∞ g U ∧ g p₀ = x₀ ∧
        ∀ p ∈ U, G (p, g p) = 0 := by
  have hc : ContDiffAt ℝ ∞ G (p₀, x₀) :=
    hG.contDiffAt ((hP.prod isOpen_univ).mem_nhds ⟨hp₀, mem_univ _⟩)
  let g := hc.implicitFunction (by simp) hinv
  have hbase : g p₀ = x₀ := hc.implicitFunction_apply_self (by simp) hinv
  have hcg : ContDiffAt ℝ ∞ g p₀ := hc.contDiffAt_implicitFunction (by simp) hinv
  have hcont : ∀ᶠ p in 𝓝 p₀, ContinuousAt g p := by
    filter_upwards [(hcg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)]
      with p hp
    exact hp.continuousAt
  have hderiv : ContinuousAt
      (fun z : E × X ↦ (fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ E X))
      (p₀, x₀) := (hc.continuousAt_fderiv (by simp)).clm_comp continuousAt_const
  have hgraph : ContinuousAt (fun p ↦ (p, g p)) p₀ :=
    continuousAt_id.prodMk hcg.continuousAt
  have hderivgraph : ContinuousAt
      (fun p ↦ (fderiv ℝ G (p, g p)).comp (ContinuousLinearMap.inr ℝ E X)) p₀ := by
    have hd : ContinuousAt
        (fun z : E × X ↦ (fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ E X))
        (p₀, g p₀) := by simpa only [hbase] using hderiv
    exact ContinuousAt.comp (f := fun p : E ↦ (p, g p)) hd hgraph
  have hiv : ∀ᶠ p in 𝓝 p₀,
      (fderiv ℝ G (p, g p) ∘L ContinuousLinearMap.inr ℝ E X).IsInvertible := by
    have h := hderivgraph.eventually (hbase.symm ▸ hinv.eventually_nhds)
    exact h
  have heq : ∀ᶠ p in 𝓝 p₀, G (p, g p) = 0 := by
    simpa [hzero] using hc.eventually_apply_implicitFunction (by simp) hinv
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
    ((show ∀ᶠ p in 𝓝 p₀, p ∈ P from hP.mem_nhds hp₀).and (hcont.and (hiv.and heq)))
  have hUP : U ⊆ P := fun p hp ↦ (hUsub hp).1
  refine ⟨U, hU, hpU, hUP, g, ?_, hbase, fun p hp ↦ (hUsub hp).2.2.2⟩
  exact balanced_implicit_recenter_smooth U hU G g
    (hG.mono (Set.prod_mono hUP Subset.rfl))
    (fun p hp ↦ (hUsub hp).2.1.continuousWithinAt)
    (fun p hp ↦ (hUsub hp).2.2.2) (fun p hp ↦ (hUsub hp).2.2.1)

#print axioms balanced_implicit_local_solution

end GlobalEmbedding.Paper
