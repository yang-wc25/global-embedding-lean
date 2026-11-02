import GlobalEmbedding.Paper.BalancedPairingRightInverse
import GlobalEmbedding.Paper.FreeSymmetricColumnCount
import Mathlib.Order.Sym2

/-!
# Full derivative pairing and the scaled right-inverse identity

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 376–414.
DAG node: `balanced-pairing`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual complete data tuple has exactly `a + s_a` coordinates.
Mathlib's sorting equivalence identifies each once-indexed pair with an unordered pair,
and the sum index adds precisely the first columns. This includes `a = 0`. -/
theorem balanced_pairing_index_card (a : ℕ) :
    Fintype.card (BalancedPairingIndex a) = a + freeSymmetricColumnCount a := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact congrArg (a + ·) (Fintype.card_congr (Sym2.sortEquiv (α := Fin a)).symm)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The full first/second pairing has exactly its source coordinates; its inverse
condition is on every datum, with no range restriction. All equalities are by evaluation
of the actual tuple operator, and the inverse characterization is extensionality.
Source: the complete first/second pairing definition in `lem:balanced`. -/
theorem balanced_pairing_specification {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ∀ x : M, TangentSpace I x) (x : M)
    (C : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) :
    (∀ u i, balancedPairingMap P D x u (Sum.inl i) =
      inner ℝ (balancedDirectionalDerivative P (D i) x) u) ∧
    (∀ u (ij : {p : Fin a × Fin a // p.1 ≤ p.2}),
      balancedPairingMap P D x u (Sum.inr ij) = inner ℝ
        (balancedDirectionalDerivative (balancedDirectionalDerivative P (D ij.val.2))
          (D ij.val.1) x) u) ∧
    (IsBalancedPairingRightInverse P D x C ↔
      ∀ z, balancedPairingMap P D x (C z) = z) := by
  refine ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_⟩
  constructor
  · intro h z
    exact congrArg (fun T ↦ T z) h
  · intro h
    apply ContinuousLinearMap.ext
    exact h

/-- The scaled fixed equation yields the full actual pairing for `U = ε v`.
Apply the actual pairing to the fixed equation, use `T C = Id`, and bilinearity to
identify `ε² Q(v,v)` with `Q(εv,εv)`. The proof uses no image condition on `C` and
works even at zero whenever such a right inverse exists. The source applies it for
nonzero ε, where `ε C` is the smoothly extended normalized inverse. -/
theorem balanced_pairing_scaled_fixed_point {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ∀ x : M, TangentSpace I x) (x : M)
    (C : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (hC : IsBalancedPairingRightInverse P D x C)
    (ε : ℝ) (Q : EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (BalancedPairingIndex a))
    (d : EuclideanSpace ℝ (BalancedPairingIndex a))
    (v : EuclideanSpace ℝ (Fin N)) (hv : v = (ε • C) (d + Q v v)) :
    balancedPairingMap P D x (ε • v) = ε ^ 2 • d + Q (ε • v) (ε • v) := by
  have hCv (z : EuclideanSpace ℝ (BalancedPairingIndex a)) :
      balancedPairingMap P D x (C z) = z := congrArg (fun T ↦ T z) hC
  calc
    balancedPairingMap P D x (ε • v) =
        ε • balancedPairingMap P D x v := map_smul _ _ _
    _ = ε • balancedPairingMap P D x ((ε • C) (d + Q v v)) := by rw [← hv]
    _ = ε ^ 2 • d + Q (ε • v) (ε • v) := by
      simp only [smul_apply, map_smul, hCv, smul_add, smul_smul,
        pow_two]

end GlobalEmbedding.Paper
