import GlobalEmbedding.Paper.BalancedPairingColumns
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual finite-sum vertical C² size

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines371–418.
DAG node: `balanced-vertical-c2-size`.
-/

open Manifold
open scoped ContDiff BigOperators

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual value, first vertical derivatives and all ordered second vertical
derivatives, using exactly the actual native derivative in the original pairing.
A uniform bound on this finite sum is the vertical C² bound used in the target;
componentwise bounds are equivalent up to the fixed factor1+a+a². No auxiliary
norm on source tangent spaces or derivative surrogate is introduced.
Source: `lem:balanced`, vertical C² O(epsilon²), lines371–378. -/
noncomputable def balancedVerticalC2Size {a N : ℕ}
    (D : Fin a → ∀ x : M, TangentSpace I x)
    (U : M → EuclideanSpace ℝ (Fin N)) (x : M) : ℝ :=
  ‖U x‖ + (∑ i, ‖balancedDirectionalDerivative U (D i) x‖) +
    ∑ i, ∑ j, ‖balancedDirectionalDerivative
      (balancedDirectionalDerivative U (D j)) (D i) x‖

/-- The actual finite vertical C² sum is nonnegative: every summand is a norm. -/
theorem balancedVerticalC2Size_nonneg {a N : ℕ}
    (D : Fin a → ∀ x : M, TangentSpace I x)
    (U : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    0 ≤ balancedVerticalC2Size D U x := by
  unfold balancedVerticalC2Size
  positivity

/-- A bound on the actual vertical finite sum controls every actual component.
Proof: each norm is nonnegative and each selected summand is at most its finite
sum. Add the other nonnegative terms. Source: `lem:balanced` vertical C² convention. -/
theorem balancedVerticalC2Size_components_le {a N : ℕ}
    (D : Fin a → ∀ x : M, TangentSpace I x)
    (U : M → EuclideanSpace ℝ (Fin N)) (x : M) {B : ℝ}
    (hB : balancedVerticalC2Size D U x ≤ B) :
    ‖U x‖ ≤ B ∧
      (∀ i, ‖balancedDirectionalDerivative U (D i) x‖ ≤ B) ∧
      ∀ i j, ‖balancedDirectionalDerivative
        (balancedDirectionalDerivative U (D j)) (D i) x‖ ≤ B := by
  have hfirst : 0 ≤ ∑ i, ‖balancedDirectionalDerivative U (D i) x‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hsecond : 0 ≤ ∑ i, ∑ j, ‖balancedDirectionalDerivative
      (balancedDirectionalDerivative U (D j)) (D i) x‖ :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  dsimp only [balancedVerticalC2Size] at hB
  refine ⟨by linarith, ?_, ?_⟩
  · intro i
    have hi := Finset.single_le_sum (f := fun i ↦ ‖balancedDirectionalDerivative U (D i) x‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
    linarith [norm_nonneg (U x)]
  · intro i j
    have hj := Finset.single_le_sum
      (f := fun j ↦ ‖balancedDirectionalDerivative
        (balancedDirectionalDerivative U (D j)) (D i) x‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
    have hi := Finset.single_le_sum
      (f := fun i ↦ ∑ j, ‖balancedDirectionalDerivative
        (balancedDirectionalDerivative U (D j)) (D i) x‖)
      (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)) (Finset.mem_univ i)
    linarith [norm_nonneg (U x)]

/-- Common bounds on the actual components bound the actual vertical finite sum
by the fixed factor1+a+a². Proof: sum the actual first/second component bounds
and count the finite index sets. Source: `lem:balanced` vertical C² norm equivalence. -/
theorem balancedVerticalC2Size_le_of_components {a N : ℕ}
    (D : Fin a → ∀ x : M, TangentSpace I x)
    (U : M → EuclideanSpace ℝ (Fin N)) (x : M) (B : ℝ)
    (hvalue : ‖U x‖ ≤ B)
    (hfirst : ∀ i, ‖balancedDirectionalDerivative U (D i) x‖ ≤ B)
    (hsecond : ∀ i j, ‖balancedDirectionalDerivative
      (balancedDirectionalDerivative U (D j)) (D i) x‖ ≤ B) :
    balancedVerticalC2Size D U x ≤ (1 + (a : ℝ) + (a : ℝ) ^ 2) * B := by
  have h1 : (∑ i, ‖balancedDirectionalDerivative U (D i) x‖) ≤ (a : ℝ) * B := by
    calc
      _ ≤ ∑ _ : Fin a, B := Finset.sum_le_sum (fun i _ ↦ hfirst i)
      _ = _ := by simp
  have h2 : (∑ i, ∑ j, ‖balancedDirectionalDerivative
      (balancedDirectionalDerivative U (D j)) (D i) x‖) ≤ (a : ℝ) ^ 2 * B := by
    calc
      _ ≤ ∑ _ : Fin a, ∑ _ : Fin a, B :=
        Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hsecond i j))
      _ = _ := by simp; ring
  dsimp only [balancedVerticalC2Size]
  nlinarith

/-- With no vertical generators, the actual vertical C² size retains the value norm.
Source: empty-generator edge case of `lem:balanced`. -/
theorem balancedVerticalC2Size_zero_generators {N : ℕ}
    (D : Fin 0 → ∀ x : M, TangentSpace I x)
    (U : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    balancedVerticalC2Size D U x = ‖U x‖ := by
  simp [balancedVerticalC2Size]

#print axioms balancedVerticalC2Size
#print axioms balancedVerticalC2Size_components_le
#print axioms balancedVerticalC2Size_le_of_components
#print axioms balancedVerticalC2Size_zero_generators

end GlobalEmbedding.Paper
