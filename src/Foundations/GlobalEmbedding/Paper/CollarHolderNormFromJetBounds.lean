import GlobalEmbedding.Paper.CollarPeriodicHolderFromLipschitz
import GlobalEmbedding.Paper.PeriodicCAlphaSpace

/-!
# Bound the actual periodic Hölder norm by spatial jet bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Uniform Taylor estimates with three spatial derivatives must control
the actual C^{2,1/2} norm, rather than a pointwise or arbitrary replacement norm.
-/

open Set WithLp
open scoped NNReal

namespace GlobalEmbedding.Paper

/-- Finite bounds on the spatial jets and a Lipschitz bound on the top jet give the stated
upper bound for the actual periodic Hölder norm.

Source: Proposition `prop:collar`, proof lines 530–534, three-spatial-derivative Taylor estimate.
Each derivative supremum in the actual norm is bounded by its supplied cube bound C_j.
Derivatives of the periodic lift remain periodic by the translation derivative identity.
Apply the flat-torus Lipschitz-to-Hölder estimate to the top jet, giving quotient bound
L D^(1-α). Its real supremum has the same bound, including the empty quotient set because
the bound is nonnegative. Add the finitely many derivative bounds and that seminorm bound.
The norm is exactly the published periodicCAlphaNorm formula; no new norm is substituted.
-/
theorem collar_holder_norm_from_jet_bounds
    {a N k : ℕ} {α : ℝ} (f : PeriodicCAlphaFunction a N k α)
    (C : ℕ → ℝ)
    (hC : ∀ j ≤ k, ∀ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) → ‖iteratedFDeriv ℝ j f.toFun x‖ ≤ C j)
    (L : ℝ≥0) (hlip : LipschitzWith L (iteratedFDeriv ℝ k f.toFun))
    (hα : α ≤ 1) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D) :
    ‖f‖ ≤ (∑ j ∈ Finset.range (k + 1), C j) + (L : ℝ) * D ^ (1 - α) := by
  have hD : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  have hderiv (j : ℕ) (hj : j ≤ k) :
      sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
        (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j f.toFun x‖} ≤ C j := by
    have hCnonneg : 0 ≤ C j :=
      (norm_nonneg _).trans (hC j hj 0 (by simp))
    apply Real.sSup_le _ hCnonneg
    rintro r ⟨x, hx, rfl⟩
    exact hC j hj x hx
  have hperiodic (x : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ) :
      iteratedFDeriv ℝ k f.toFun (x + toLp 2 (fun i ↦ (n i : ℝ))) =
        iteratedFDeriv ℝ k f.toFun x := by
    have heq : (fun z ↦ f.toFun (z + toLp 2 (fun i ↦ (n i : ℝ)))) = f.toFun :=
      funext (fun z ↦ f.periodic z n)
    have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f.toFun) k
      (toLp 2 (fun i ↦ (n i : ℝ))) x
    simpa only [heq] using ht.symm
  have hquotient := collar_periodic_holder_from_lipschitz
    (iteratedFDeriv ℝ k f.toFun) hperiodic L hlip α hα D hdiam
  have hholder :
      sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
        let d := dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
        0 < d ∧ r = ‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ / d ^ α} ≤
        (L : ℝ) * D ^ (1 - α) := by
    apply Real.sSup_le _ (mul_nonneg L.coe_nonneg (Real.rpow_nonneg hD _))
    rintro r ⟨x, y, hd, rfl⟩
    exact hquotient x y hd
  change periodicCAlphaNorm f ≤ _
  unfold periodicCAlphaNorm
  exact add_le_add (Finset.sum_le_sum (fun j hj ↦
    hderiv j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) hholder

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_norm_from_jet_bounds
