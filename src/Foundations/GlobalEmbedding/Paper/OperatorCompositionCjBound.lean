import GlobalEmbedding.Paper.FiniteCjNormSpecification
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization` proof, line822, quantitative normal projection products. -/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Explicit actual Cj bounds for composition of smooth heterogeneous operator fields.

Proof: the bilinear composition map has norm at most1. Its kth iterated derivative
is bounded by the binomial sum, at most2^k ab. Equality on the open U transfers
this to V. These bounds establish finiteness before taking actual suprema and
summing. Source: `prop:initialization` proof, line822. Empty/zero spaces retained. -/
theorem operator_composition_cj_bound
    {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (j : ℕ) (U : Set D) (hU : IsOpen U)
    (L : D → F →L[ℝ] G) (R : D → E →L[ℝ] F) (V : D → E →L[ℝ] G)
    (hL : ContDiffOn ℝ ∞ L U) (hR : ContDiffOn ℝ ∞ R U)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLb : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k L x‖ ≤ a)
    (hRb : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k R x‖ ≤ b)
    (hV : Set.EqOn V (fun x ↦ (L x).comp (R x)) U) :
    (∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k V x‖ ≤ 2 ^ k * a * b) ∧
    (∀ k ≤ j, BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k V x‖)) ∧
    finiteCjNorm j V U ≤ (∑ k ∈ Finset.range (j + 1), (2 : ℝ) ^ k) * a * b := by
  have hprod : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k V x‖ ≤ 2 ^ k * a * b := by
    intro k hk x hx
    rw [← iteratedFDerivWithin_of_isOpen k hU hx, iteratedFDerivWithin_congr hV hx]
    have he := (ContinuousLinearMap.compL ℝ E F G)
      |>.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hL hR hU.uniqueDiffOn hx
        (n := k) (by simp) (ContinuousLinearMap.norm_compL_le ℝ E F G)
    refine he.trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a * b := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ k := by simpa using hi
        have hli : ‖iteratedFDerivWithin ℝ i L U x‖ ≤ a := by
          rw [iteratedFDerivWithin_of_isOpen i hU hx]
          exact hLb i (hik.trans hk) x hx
        have hri : ‖iteratedFDerivWithin ℝ (k - i) R U x‖ ≤ b := by
          rw [iteratedFDerivWithin_of_isOpen (k - i) hU hx]
          exact hRb (k - i) (by omega) x hx
        gcongr
      _ = 2 ^ k * a * b := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose k
  have hbdd : ∀ k ≤ j,
      BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k V x‖) := by
    intro k hk
    exact ⟨2 ^ k * a * b, by rintro _ ⟨x, rfl⟩; exact hprod k hk x x.property⟩
  refine ⟨hprod, hbdd, ?_⟩
  have he := (finiteCjNorm_specification j V U hbdd).2.2.1
    (fun k ↦ 2 ^ k * a * b) (by intros; positivity) hprod
  simpa only [← Finset.sum_mul] using he

end GlobalEmbedding.Paper
