import GlobalEmbedding.Paper.PeriodicCAlphaBilinear

/-!
# Full original periodic Hölder norm bound for actual bilinear multiplication

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-bilinear-norm-bound`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The FULL original norm of the constructed actual bilinear product obeys a finite explicit
binomial/diameter bound times the two original input norms.

Take each actual finite real jet supremum using the proved product jet estimate, and take
the actual top flat-torus Holder supremum using its proved quotient estimate. Add them and
factor the input norms. Nonnegative bounds handle empty quotient sets without conventions
for unbounded suprema. Source: bounded Holder multiplication in `lem:balanced`. -/
theorem periodicCAlphaBilinear_norm {a M N L k : ℕ} {α : ℝ}
    (B : EuclideanSpace ℝ (Fin M) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin L))
    (hα : α ≤ 1) (f : PeriodicCAlphaFunction a M k α) (g : PeriodicCAlphaFunction a N k α)
    (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D) :
    ‖periodicCAlphaBilinear B hα f g‖ ≤
      ‖B‖ * ((∑ j ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) +
        2 * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (1 + D ^ (1 - α))) * ‖f‖ * ‖g‖ := by
  let S (j : ℕ) := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
  have hS (j : ℕ) : 0 ≤ S j := Finset.sum_nonneg (fun i hi ↦ Nat.cast_nonneg _)
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  have hC : 0 ≤ 1 + D ^ (1 - α) := by positivity
  have hjet (j : ℕ) (hj : j ≤ k) :
      sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
        (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧
        r = ‖iteratedFDeriv ℝ j (periodicCAlphaBilinear B hα f g).toFun x‖} ≤
        ‖B‖ * S j * ‖f‖ * ‖g‖ := by
    apply Real.sSup_le _ (by positivity)
    rintro r ⟨x, hx, rfl⟩
    exact periodicCAlpha_bilinear_jet_bound B f g j hj x
  have hholder :
      sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
        let d := dist
          (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
        0 < d ∧ r =
          ‖iteratedFDeriv ℝ k (periodicCAlphaBilinear B hα f g).toFun x -
            iteratedFDeriv ℝ k (periodicCAlphaBilinear B hα f g).toFun y‖ / d ^ α} ≤
        2 * ‖B‖ * S k * (1 + D ^ (1 - α)) * ‖f‖ * ‖g‖ := by
    apply Real.sSup_le _ (by positivity)
    rintro r ⟨x, y, hd, rfl⟩
    exact periodicCAlpha_bilinear_quotient_bound B f g hα D hdiam x y hd
  change periodicCAlphaNorm (periodicCAlphaBilinear B hα f g) ≤ _
  unfold periodicCAlphaNorm
  calc
    _ ≤ (∑ j ∈ Finset.range (k + 1), ‖B‖ * S j * ‖f‖ * ‖g‖) +
        2 * ‖B‖ * S k * (1 + D ^ (1 - α)) * ‖f‖ * ‖g‖ :=
      add_le_add (Finset.sum_le_sum (fun j hj ↦ hjet j
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) hholder
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      change ‖B‖ * (∑ j ∈ Finset.range (k + 1), S j) * ‖f‖ * ‖g‖ +
        2 * ‖B‖ * S k * (1 + D ^ (1 - α)) * ‖f‖ * ‖g‖ =
        ‖B‖ * ((∑ j ∈ Finset.range (k + 1), S j) +
          2 * S k * (1 + D ^ (1 - α))) * ‖f‖ * ‖g‖
      ring

#print axioms periodicCAlphaBilinear_norm

end GlobalEmbedding.Paper
