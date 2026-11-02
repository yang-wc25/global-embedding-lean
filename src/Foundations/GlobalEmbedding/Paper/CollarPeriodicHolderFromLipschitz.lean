import GlobalEmbedding.Paper.PeriodicFlatTorusMinimum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Abel

/-!
# Flat-torus Hölder control from a periodic lift's Lipschitz bound

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Uniform control of one more spatial derivative turns C³ Taylor remainder
bounds into C^{2,1/2} bounds. The estimate must use the actual flat-torus distance, not the
possibly much larger distance between arbitrarily chosen real lifts.
-/

open WithLp
open scoped NNReal

namespace GlobalEmbedding.Paper

/-- A periodic globally Lipschitz lift has a flat-torus Hölder quotient bound at every exponent
at most one. A diameter bound D contributes the factor D^(1-α).

Source: Proposition `prop:collar`, proof lines 530–534, Taylor estimates with three spatial
derivatives. Choose the attained minimizing integer-lattice representative of the distance from
x to y. Integer periodicity identifies the value at y with the value at that representative.
The global Lipschitz estimate therefore gives `‖g(x)-g(y)‖≤L*d_T(x,y)`. Divide by d_T^α when
the torus distance is positive, rewrite the ratio as L*d_T^(1-α), and use d_T≤D and α≤1.
The zero-dimensional torus and zero-distance pairs require no quotient estimate, precisely as in
the actual periodic Hölder carrier. No positive-diameter hypothesis is added.
-/
theorem collar_periodic_holder_from_lipschitz
    {a : ℕ} {V : Type*} [NormedAddCommGroup V]
    (g : EuclideanSpace ℝ (Fin a) → V)
    (hperiodic : ∀ (x : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ),
      g (x + toLp 2 (fun i ↦ (n i : ℝ))) = g x)
    (L : ℝ≥0) (hlip : LipschitzWith L g) (α : ℝ) (hα : α ≤ 1)
    (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D) :
    ∀ x y : EuclideanSpace ℝ (Fin a),
      let d := dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
      0 < d → ‖g x - g y‖ / d ^ α ≤ (L : ℝ) * D ^ (1 - α) := by
  intro x y
  dsimp only
  let d := dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
    (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
  change 0 < d → ‖g x - g y‖ / d ^ α ≤ (L : ℝ) * D ^ (1 - α)
  intro hd
  obtain ⟨n, hmin, hminimal⟩ := periodic_flat_torus_distance_minimum x y
  have hdiff : x - (y + toLp 2 (fun i ↦ (n i : ℝ))) =
      x - y - toLp 2 (fun i ↦ (n i : ℝ)) := by abel
  have hbound : ‖g x - g y‖ ≤ (L : ℝ) * d := by
    calc
      ‖g x - g y‖ = ‖g x - g (y + toLp 2 (fun i ↦ (n i : ℝ)))‖ := by
        rw [hperiodic y n]
      _ ≤ (L : ℝ) * ‖x - (y + toLp 2 (fun i ↦ (n i : ℝ)))‖ :=
        hlip.norm_sub_le _ _
      _ = (L : ℝ) * d := by rw [hdiff, ← hmin]
  calc
    ‖g x - g y‖ / d ^ α ≤ ((L : ℝ) * d) / d ^ α :=
      div_le_div_of_nonneg_right hbound (Real.rpow_nonneg hd.le _)
    _ = (L : ℝ) * d ^ (1 - α) := by rw [Real.rpow_sub hd, Real.rpow_one]; ring
    _ ≤ (L : ℝ) * D ^ (1 - α) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le (hdiam x y) (sub_nonneg.mpr hα))
        L.coe_nonneg

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_periodic_holder_from_lipschitz
