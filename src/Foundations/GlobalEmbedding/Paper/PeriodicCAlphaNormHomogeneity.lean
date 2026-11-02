import GlobalEmbedding.Paper.PeriodicCAlphaNorm
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations
import Mathlib.Basic.Real.Pointwise

/-!
# Scalar homogeneity of the actual periodic Hölder formula

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-norm-homogeneity`.
-/

open Set WithLp
open scoped Pointwise

namespace GlobalEmbedding.Paper

/-- The actual periodic Hölder formula is absolutely homogeneous under its actual real
vector-space scalar multiplication.

Proof: every iterated derivative and top derivative difference scales by c, so its norm
scales by `‖c‖`. Real suprema commute with multiplication by this nonnegative number,
including zero scalars and empty Hölder-quotient sets. Distribute over the finite sum.
Source: `lem:balanced`, usual periodic Hölder norm expansion. -/
theorem periodicCAlphaNorm_homogeneous {a N k : ℕ} {α : ℝ}
    (c : ℝ) (f : PeriodicCAlphaFunction a N k α) :
    periodicCAlphaNorm (c • f) = ‖c‖ * periodicCAlphaNorm f := by
  have hsup {ι : Type} (S : Set ι) (F : ι → ℝ) :
      sSup {r : ℝ | ∃ x ∈ S, r = ‖c‖ * F x} =
        ‖c‖ * sSup {r : ℝ | ∃ x ∈ S, r = F x} := by
    have heq : {r : ℝ | ∃ x ∈ S, r = ‖c‖ * F x} =
        ‖c‖ • {r : ℝ | ∃ x ∈ S, r = F x} := by
      ext r
      change (∃ x ∈ S, r = ‖c‖ * F x) ↔
        ∃ t, (∃ x ∈ S, t = F x) ∧ ‖c‖ * t = r
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨F x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨t, ⟨x, hx, rfl⟩, hr⟩
        exact ⟨x, hx, hr.symm⟩
    rw [heq, Real.sSup_smul_of_nonneg (norm_nonneg c)]
    rfl
  let D (u : PeriodicCAlphaFunction a N k α) (j : ℕ) :=
    sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j u.toFun x‖}
  let H (u : PeriodicCAlphaFunction a N k α) :=
    sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
      let d := dist
        (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
      0 < d ∧ r = ‖iteratedFDeriv ℝ k u.toFun x - iteratedFDeriv ℝ k u.toFun y‖ / d ^ α}
  have hD (j : ℕ) (hj : j ≤ k) : D (c • f) j = ‖c‖ * D f j := by
    dsimp only [D]
    simp_rw [(periodicCAlpha_pointwise_operations a N k α).2.2 c f,
      iteratedFDeriv_const_smul_apply (f.contDiff.of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul]
    exact hsup {x : EuclideanSpace ℝ (Fin a) | ∀ i, x i ∈ Icc (0 : ℝ) 1}
      (fun x ↦ ‖iteratedFDeriv ℝ j f.toFun x‖)
  have hH : H (c • f) = ‖c‖ * H f := by
    dsimp only [H]
    simp_rw [(periodicCAlpha_pointwise_operations a N k α).2.2 c f,
      iteratedFDeriv_const_smul_apply f.contDiff.contDiffAt, ← smul_sub, norm_smul,
      mul_div_assoc]
    simpa only [Prod.exists, Set.mem_ofPred_eq] using hsup
      {z : EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin a) |
        0 < dist (toLp 2 (fun i : Fin a ↦ (z.1 i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (z.2 i : AddCircle (1 : ℝ))))}
      (fun z ↦ ‖iteratedFDeriv ℝ k f.toFun z.1 - iteratedFDeriv ℝ k f.toFun z.2‖ /
        dist (toLp 2 (fun i : Fin a ↦ (z.1 i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (z.2 i : AddCircle (1 : ℝ)))) ^ α)
  change (∑ j ∈ Finset.range (k + 1), D (c • f) j) + H (c • f) =
    ‖c‖ * ((∑ j ∈ Finset.range (k + 1), D f j) + H f)
  rw [hH]
  rw [Finset.sum_congr rfl (fun j hj ↦ hD j (Nat.le_of_lt_succ
    (Finset.mem_range.mp hj)))]
  simp only [Finset.mul_sum, mul_add]

#print axioms periodicCAlphaNorm_homogeneous

end GlobalEmbedding.Paper
