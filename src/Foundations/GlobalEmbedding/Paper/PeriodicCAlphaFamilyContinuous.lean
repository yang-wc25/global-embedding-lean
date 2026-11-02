import GlobalEmbedding.Paper.PeriodicCAlphaHigherJetConvergence
import GlobalEmbedding.Paper.PeriodicUniformFamily

/-!
# Actual Hölder norm continuity of jointly continuous one-higher-jet families

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-joint-jet-family-continuity`.
-/

namespace GlobalEmbedding.Paper

/-- Actual C^{k+1} periodic lift slices with jointly continuous spatial jets through k+1 vary
continuously in the ORIGINAL full C^{k,α} norm for α≤1.

Proof: each actual jet is integer-periodic. Joint continuity and compact-cube reduction give
global uniform convergence of each jet at every parameter. The one-higher-jet convergence
criterion then gives convergence in the full actual Hölder norm.
Source: norm-valued parameter slices in the proof of `lem:balanced`. -/
theorem periodicCAlpha_family_continuous {P : Type*} [UniformSpace P]
    [WeaklyLocallyCompactSpace P] {a N k : ℕ} {α : ℝ}
    (F : P → PeriodicCAlphaFunction a N k α)
    (hF : ∀ p, ContDiff ℝ (k + 1) (F p).toFun)
    (hjet : ∀ j ≤ k + 1, Continuous (fun z : P × EuclideanSpace ℝ (Fin a) ↦
      iteratedFDeriv ℝ j (F z.1).toFun z.2)) (hα : α ≤ 1) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro p
  apply periodicCAlpha_tendsto_of_higher_uniform_jets F (F p) hF (hF p) _ hα
  intro j hj
  apply periodic_uniform_family _ (hjet j hj) _ p
  intro q x n
  have heq : (fun z ↦ (F q).toFun (z + WithLp.toLp 2 (fun i ↦ (n i : ℝ)))) = (F q).toFun :=
    funext (fun z ↦ (F q).periodic z n)
  have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := (F q).toFun) j
    (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) x
  simpa only [heq] using ht.symm

#print axioms periodicCAlpha_family_continuous

end GlobalEmbedding.Paper
