import GlobalEmbedding.Paper.PeriodicFlatTorusLiftSmoothTransfer
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Actual flat-torus local quotient-inverse chart transitions are genuinely smooth

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-chart-transition`.
-/

open Set WithLp

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The coordinate transition between actual quotient-inverse charts is genuinely C^n.

On its actual open source the transition is continuous. Its quotient projection is the
original projection of the coordinate point, by the genuine chart inverse identities.
Compare it to the identity lift using the proved smooth-lift transfer theorem. This proves
all real differentiability orders, including true C∞ and analyticity, on the whole overlap.
Source: fiber chart transitions in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_chart_transition_contDiff {a : ℕ} (n : ℕ∞ω)
    (e e' : OpenPartialHomeomorph
      (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) (EuclideanSpace ℝ (Fin a)))
    (he : (e.symm : EuclideanSpace ℝ (Fin a) → PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) =
      fun x ↦ toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
    (he' : (e'.symm : EuclideanSpace ℝ (Fin a) → PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) =
      fun x ↦ toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ)))) :
    ContDiffOn ℝ n (e.symm.trans e') (e.symm.trans e').source := by
  apply periodic_flat_torus_lift_contDiffOn (e.symm.trans e').source
    (e.symm.trans e').open_source (e.symm.trans e') id
    (e.symm.trans e').continuousOn contDiffOn_id
  intro x hx
  change x ∈ e.target ∧ e.symm x ∈ e'.source at hx
  exact (congrFun he' (e' (e.symm x))).symm.trans
    ((e'.left_inv hx.2).trans (congrFun he x))

#print axioms periodic_flat_torus_chart_transition_contDiff

end GlobalEmbedding.Paper
