import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smoothness of continuous implicit branches

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 418–425; agent expansion by the Banach implicit function theorem.
DAG node: `balanced-implicit-recenter-smooth`.
-/

open Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A continuous zero branch with invertible vertical derivative is smooth on its open domain.

Proof: at each point apply the smooth implicit function theorem. Continuity places the given
branch inside its local uniqueness neighborhood. The zero equation then identifies it locally
with the smooth implicit function. Smoothness is local on the open domain.
Source: proof of `lem:balanced`, lines 418–425, implicit-function expansion. -/
theorem balanced_implicit_recenter_smooth
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (U : Set E) (hU : IsOpen U) (G : E × X → X) (g : E → X)
    (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ)) (hg : ContinuousOn g U)
    (hzero : ∀ p ∈ U, G (p, g p) = 0)
    (hinv : ∀ p ∈ U,
      (fderiv ℝ G (p, g p) ∘L ContinuousLinearMap.inr ℝ E X).IsInvertible) :
    ContDiffOn ℝ ∞ g U := by
  apply hU.contDiffOn_iff.mpr
  intro p hp
  have hc : ContDiffAt ℝ ∞ G (p, g p) :=
    hG.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
  have hi := hinv p hp
  have hgraph : ContinuousAt (fun q ↦ (q, g q)) p :=
    continuousAt_id.prodMk ((hg p hp).continuousAt (hU.mem_nhds hp))
  have heq := hgraph.eventually
    (hc.eventually_apply_eq_iff_implicitFunction (by simp) hi)
  apply (hc.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq
  filter_upwards [heq, hU.mem_nhds hp] with q hq hqU
  exact ((hq.mp ((hzero q hqU).trans (hzero p hp).symm))).symm

#print axioms balanced_implicit_recenter_smooth

end GlobalEmbedding.Paper
