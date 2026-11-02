import GlobalEmbedding.Paper.PeriodicFlatTorusLiftsLocallyConstant
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Transfer genuine smoothness between continuous lifts of the same actual torus map

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-flat-torus-lift-smooth-transfer`.
-/

open Set WithLp
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A continuous actual Euclidean lift of the same torus map as a genuine C^n lift is C^n.

Their actual vector difference is locally constant by the proved local lifting theorem.
Near each parameter point, the first lift is the second lift plus one fixed vector, hence
has the same genuine differentiability order. This includes true C∞ as well as finite
orders and analyticity, without assuming a smooth quotient instance.
Source: local torus parameter coordinates in the proof of `lem:balanced`. -/
theorem periodic_flat_torus_lift_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {a : ℕ} {n : ℕ∞ω}
    (U : Set P) (hU : IsOpen U) (F G : P → EuclideanSpace ℝ (Fin a))
    (hF : ContinuousOn F U) (hG : ContDiffOn ℝ n G U)
    (hπ : ∀ p ∈ U, toLp 2 (fun i : Fin a ↦ (F p i : AddCircle (1 : ℝ))) =
      toLp 2 (fun i : Fin a ↦ (G p i : AddCircle (1 : ℝ)))) : ContDiffOn ℝ n F U := by
  apply hU.contDiffOn_iff.mpr
  intro p hp
  have hnear := periodic_flat_torus_lifts_eventually_sub_eq U hU F G hF hG.continuousOn hπ p hp
  apply ((hG.contDiffAt (hU.mem_nhds hp)).add
    (contDiffAt_const (c := F p - G p))).congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hq)

#print axioms periodic_flat_torus_lift_contDiffOn

end GlobalEmbedding.Paper
