import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic.Abel

/-!
# Compare Euclidean jet Hölder bounds with the original periodic norm

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382; the periodic Schauder estimate uses the actual flat-torus Hölder norm.
DAG node: `balanced-inverse-norm-from-euclidean-holder`.
-/

open Set WithLp
open scoped NNReal

namespace GlobalEmbedding.Paper

/-- Global Euclidean jet bounds and a top-jet Euclidean Hölder bound control the actual
periodic norm, with no positive torus- or target-dimension assumption.

Proof: each cube jet supremum is at most C. At a positive flat-torus distance, choose an
attained minimizing integer-lattice representative. The actual iterated derivative of the
periodic lift is periodic, so its Euclidean Hölder estimate at this representative gives
exactly C times the flat distance to the exponent α. Division bounds each actual quotient
by C, hence its real supremum by C, including an empty quotient set. Add the k+1 jet
suprema and this one seminorm. The original norm formula is used throughout.
Source: `lem:balanced`, proof line 382, periodic Schauder/norm interface. -/
theorem periodicCAlphaNorm_le_of_euclidean_holder
    {a N k : ℕ} {α C : ℝ≥0} (f : PeriodicCAlphaFunction a N k (α : ℝ))
    (hjets : ∀ j ≤ k, ∀ x : EuclideanSpace ℝ (Fin a),
      ‖iteratedFDeriv ℝ j f.toFun x‖ ≤ (C : ℝ))
    (hholder : HolderWith C α (iteratedFDeriv ℝ k f.toFun)) :
    ‖f‖ ≤ (k + 2 : ℕ) * (C : ℝ) := by
  have hderiv (j : ℕ) (hj : j ≤ k) :
      sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
        (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j f.toFun x‖} ≤ C := by
    apply Real.sSup_le _ C.coe_nonneg
    rintro r ⟨x, hx, rfl⟩
    exact hjets j hj x
  have hperiodic (x : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ) :
      iteratedFDeriv ℝ k f.toFun (x + toLp 2 (fun i ↦ (n i : ℝ))) =
        iteratedFDeriv ℝ k f.toFun x := by
    have heq : (fun z ↦ f.toFun (z + toLp 2 (fun i ↦ (n i : ℝ)))) = f.toFun :=
      funext (fun z ↦ f.periodic z n)
    have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f.toFun) k
      (toLp 2 (fun i ↦ (n i : ℝ))) x
    simpa only [heq] using ht.symm
  have hquotient :
      sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
        let d := dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
        0 < d ∧ r = ‖iteratedFDeriv ℝ k f.toFun x -
          iteratedFDeriv ℝ k f.toFun y‖ / d ^ (α : ℝ)} ≤ C := by
    apply Real.sSup_le _ C.coe_nonneg
    rintro r ⟨x, y, hd, rfl⟩
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
    obtain ⟨n, hmin, _⟩ := periodic_flat_torus_distance_minimum x y
    have hdiff : x - (y + toLp 2 (fun i ↦ (n i : ℝ))) =
        x - y - toLp 2 (fun i ↦ (n i : ℝ)) := by abel
    have h := hholder.dist_le x (y + toLp 2 (fun i ↦ (n i : ℝ)))
    rw [hperiodic y n, dist_eq_norm, dist_eq_norm, hdiff, ← hmin] at h
    exact h
  change periodicCAlphaNorm f ≤ _
  unfold periodicCAlphaNorm
  calc
    _ ≤ (∑ _j ∈ Finset.range (k + 1), (C : ℝ)) + C :=
      add_le_add (Finset.sum_le_sum (fun j hj ↦
        hderiv j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) hquotient
    _ = (k + 2 : ℕ) * (C : ℝ) := by simp; ring

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.periodicCAlphaNorm_le_of_euclidean_holder
