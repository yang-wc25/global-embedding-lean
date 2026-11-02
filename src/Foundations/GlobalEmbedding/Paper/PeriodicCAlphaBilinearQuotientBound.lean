import GlobalEmbedding.Paper.PeriodicCAlphaAllJetHolder
import GlobalEmbedding.Paper.BilinearJetDifference

/-!
# Actual flat-torus top Hölder quotient bound for a bilinear product

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-bilinear-top-quotient-bound`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- The actual top flat-torus Hölder quotient of B(f,g) is bounded by the original input norms,
with a finite binomial and diameter constant, using only the declared input regularity.

Apply the genuine Leibniz endpoint-difference bound. Each input jet difference has its actual
flat Hölder bound, and each remaining input jet is bounded by the original norm. Factor the
positive-distance power from the finite sum and divide by it.
Source: the full Hölder bilinear multiplication estimate in `lem:balanced`. -/
theorem periodicCAlpha_bilinear_quotient_bound {a M N L k : ℕ} {α : ℝ}
    (B : EuclideanSpace ℝ (Fin M) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin L))
    (f : PeriodicCAlphaFunction a M k α) (g : PeriodicCAlphaFunction a N k α)
    (hα : α ≤ 1) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D)
    (x y : EuclideanSpace ℝ (Fin a))
    (hd : 0 < dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
      (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))) :
    ‖iteratedFDeriv ℝ k (fun z ↦ B (f.toFun z) (g.toFun z)) x -
        iteratedFDeriv ℝ k (fun z ↦ B (f.toFun z) (g.toFun z)) y‖ /
        dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ^ α ≤
      2 * ‖B‖ * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) *
        (1 + D ^ (1 - α)) * ‖f‖ * ‖g‖ := by
  let d := dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
    (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
  let C := 1 + D ^ (1 - α)
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  have hC : 0 ≤ C := add_nonneg zero_le_one (Real.rpow_nonneg hD0 _)
  have hp : 0 < d ^ α := Real.rpow_pos_of_pos hd _
  have hfdiff (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i f.toFun x - iteratedFDeriv ℝ i f.toFun y‖ ≤ C * ‖f‖ * d ^ α := by
    have hq := periodicCAlpha_all_jet_holder_bound f hα D hdiam i hi x y hd
    change _ / d ^ α ≤ C * ‖f‖ at hq
    exact (div_le_iff₀ hp).mp hq
  have hgdiff (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i g.toFun x - iteratedFDeriv ℝ i g.toFun y‖ ≤ C * ‖g‖ * d ^ α := by
    have hq := periodicCAlpha_all_jet_holder_bound g hα D hdiam i hi x y hd
    change _ / d ^ α ≤ C * ‖g‖ at hq
    exact (div_le_iff₀ hp).mp hq
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      ‖iteratedFDeriv ℝ i f.toFun x - iteratedFDeriv ℝ i f.toFun y‖ *
          ‖iteratedFDeriv ℝ (k - i) g.toFun x‖ + ‖iteratedFDeriv ℝ i f.toFun y‖ *
          ‖iteratedFDeriv ℝ (k - i) g.toFun x - iteratedFDeriv ℝ (k - i) g.toFun y‖ ≤
        2 * C * ‖f‖ * ‖g‖ * d ^ α := by
    have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hfi : ‖iteratedFDeriv ℝ i f.toFun y‖ ≤ ‖f‖ :=
      periodicCAlpha_global_jet_bound f i hi' y
    have hgi : ‖iteratedFDeriv ℝ (k - i) g.toFun x‖ ≤ ‖g‖ :=
      periodicCAlpha_global_jet_bound g (k - i) (Nat.sub_le _ _) x
    have h₁ := mul_le_mul (hfdiff i hi') hgi (norm_nonneg _)
      (mul_nonneg (mul_nonneg hC (norm_nonneg f)) hp.le)
    have h₂ := mul_le_mul hfi (hgdiff (k - i) (Nat.sub_le _ _))
      (norm_nonneg _) (norm_nonneg f)
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  change _ / d ^ α ≤ 2 * ‖B‖ * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) *
    C * ‖f‖ * ‖g‖
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i f.toFun x - iteratedFDeriv ℝ i f.toFun y‖ *
          ‖iteratedFDeriv ℝ (k - i) g.toFun x‖ + ‖iteratedFDeriv ℝ i f.toFun y‖ *
          ‖iteratedFDeriv ℝ (k - i) g.toFun x - iteratedFDeriv ℝ (k - i) g.toFun y‖) :=
      bilinear_jet_difference_bound B k f.toFun g.toFun f.contDiff g.contDiff x y
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (2 * C * ‖f‖ * ‖g‖ * d ^ α) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi ↦
        mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _))) (norm_nonneg B)
    _ = _ := by rw [← Finset.sum_mul]; ring

#print axioms periodicCAlpha_bilinear_quotient_bound

end GlobalEmbedding.Paper
