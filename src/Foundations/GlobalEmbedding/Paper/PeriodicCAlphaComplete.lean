import GlobalEmbedding.Paper.PeriodicCAlphaCauchyRegularity
import GlobalEmbedding.Paper.PeriodicCAlphaLimitMembership
import GlobalEmbedding.Paper.PeriodicCAlphaCauchyNormConvergence
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Completeness of the actual periodic Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-ambient-complete`.
-/

open Filter
open scoped Topology

namespace GlobalEmbedding.Paper

/-- The actual periodic Hölder normed ambient space is complete in its actual norm.

Proof: for a Cauchy sequence, the bounded continuous jet maps have uniform limits. The
uniform-jet Taylor argument identifies these as the actual derivatives of a genuine C^k
periodic lift. A Cauchy sequence has bounded norms; passing the actual derivative and Hölder
quotient bounds to those pointwise jet limits puts the lift in the original carrier. Finally,
the Cauchy-tail estimates pass to all difference jets and Hölder quotients, hence to their
finite real suprema and the full norm, giving norm convergence to that carrier element.
Apply the metric Cauchy-sequence completeness criterion. No completed replacement or assumed
Holder completeness is used. Source: `lem:balanced`, usual ambient Hölder completeness. -/
theorem periodicCAlpha_completeSpace (a N k : ℕ) (α : ℝ) :
    CompleteSpace (PeriodicCAlphaFunction a N k α) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨g, hg, hper, hjet, _⟩ := periodicCAlpha_cauchy_limit_regularity u hu
  obtain ⟨M, hM⟩ := hu.isBounded_range.exists_norm_le
  have hnorm (n : ℕ) : ‖u n‖ ≤ M := hM (u n) ⟨n, rfl⟩
  obtain ⟨f, hf⟩ := periodicCAlpha_limit_membership u g hg hper
    (fun j hj x ↦ (hjet j hj).tendsto_at x) M hnorm
  refine ⟨f, periodicCAlpha_cauchy_norm_tendsto u hu f ?_⟩
  intro j hj x
  rw [hf]
  exact (hjet j hj).tendsto_at x

/-- The complete-space instance for the actual periodic Hölder normed ambient space.
Source: `lem:balanced`, proof, line 382; established by the named actual completeness theorem. -/
instance periodicCAlphaCompleteSpace {a N k : ℕ} {α : ℝ} :
    CompleteSpace (PeriodicCAlphaFunction a N k α) :=
  periodicCAlpha_completeSpace a N k α

#print axioms periodicCAlpha_completeSpace
#print axioms periodicCAlphaCompleteSpace

end GlobalEmbedding.Paper
