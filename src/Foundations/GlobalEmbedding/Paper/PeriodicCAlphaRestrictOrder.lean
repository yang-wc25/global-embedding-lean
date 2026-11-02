import GlobalEmbedding.Paper.PeriodicCAlphaAllJetHolder

/-!
# Actual ambient Hölder regularity inclusion

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-raw-restrict-order`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Regard an actual C^{k,α} lift as an actual C^{j,α} lift, for j≤k and α≤1.

Keep the actual lift unchanged. Restrict differentiability and the existing derivative
bounds. Compactness gives a finite actual flat-torus diameter; the proved all-jet quotient
bound supplies the lower top Hölder witness without an extra derivative assumption.
Source: regularity levels in vertical difference quotients in the proof of `lem:balanced`. -/
noncomputable def periodicCAlphaRestrictOrder {a N k : ℕ} {α : ℝ}
    (j : ℕ) (hj : j ≤ k) (hα : α ≤ 1) (f : PeriodicCAlphaFunction a N k α) :
    PeriodicCAlphaFunction a N j α where
  toFun := f.toFun
  periodic := f.periodic
  contDiff := f.contDiff.of_le (by exact_mod_cast hj)
  derivative_bounded := fun i hi ↦ f.derivative_bounded i (hi.trans hj)
  holder_bounded := by
    have hcompact : IsCompact (univ : Set (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))) := by
      have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) →
          PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) = univ :=
        Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
      rw [← hrange]
      exact isCompact_range (PiLp.continuous_toLp _ _)
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
    refine ⟨(1 + D ^ (1 - α)) * ‖f‖, ?_⟩
    intro x y d hd
    exact periodicCAlpha_all_jet_holder_bound f hα D
      (fun x y ↦ hD (mem_univ _) (mem_univ _)) j hj x y hd

#print axioms periodicCAlphaRestrictOrder

end GlobalEmbedding.Paper
