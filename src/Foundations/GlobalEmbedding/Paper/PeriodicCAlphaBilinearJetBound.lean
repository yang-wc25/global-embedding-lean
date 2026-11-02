import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaGlobalJetBound
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual pointwise bilinear product jet bounds in terms of the original Hölder norms

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-bilinear-value-jet-bound`.
-/

namespace GlobalEmbedding.Paper

/-- Every declared-order jet of an actual pointwise bilinear product is bounded by the finite
Leibniz constant times the two original Hölder norms.

Apply Mathlib's bilinear iterated derivative bound. Each input jet in the finite sum is
bounded globally by its original norm; sum the resulting binomial coefficients.
Source: bounded Hölder multiplication in `lem:balanced`. -/
theorem periodicCAlpha_bilinear_jet_bound {a M N L k : ℕ} {α : ℝ}
    (B : EuclideanSpace ℝ (Fin M) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin L))
    (f : PeriodicCAlphaFunction a M k α) (g : PeriodicCAlphaFunction a N k α)
    (j : ℕ) (hj : j ≤ k) (x : EuclideanSpace ℝ (Fin a)) :
    ‖iteratedFDeriv ℝ j (fun z ↦ B (f.toFun z) (g.toFun z)) x‖ ≤
      ‖B‖ * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * ‖f‖ * ‖g‖ := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f.toFun x‖ *
        ‖iteratedFDeriv ℝ (j - i) g.toFun x‖ ≤ (j.choose i : ℝ) * ‖f‖ * ‖g‖ := by
    have hfi : ‖iteratedFDeriv ℝ i f.toFun x‖ ≤ ‖f‖ :=
      periodicCAlpha_global_jet_bound f i
        ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj) x
    have hgi : ‖iteratedFDeriv ℝ (j - i) g.toFun x‖ ≤ ‖g‖ :=
      periodicCAlpha_global_jet_bound g (j - i) ((Nat.sub_le _ _).trans hj) x
    exact mul_le_mul (mul_le_mul_of_nonneg_left hfi (Nat.cast_nonneg _)) hgi
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f.toFun x‖ * ‖iteratedFDeriv ℝ (j - i) g.toFun x‖ :=
      B.norm_iteratedFDeriv_le_of_bilinear f.contDiff g.contDiff x (by exact_mod_cast hj)
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖f‖ * ‖g‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (norm_nonneg B)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

#print axioms periodicCAlpha_bilinear_jet_bound

end GlobalEmbedding.Paper
