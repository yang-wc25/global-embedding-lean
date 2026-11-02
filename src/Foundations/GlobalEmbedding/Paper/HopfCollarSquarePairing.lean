import GlobalEmbedding.Paper.HopfCollarProperties
import GlobalEmbedding.Paper.FreeCorrectionStability
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual square collar pairing and its original inverse PDE rows

Source: `main.tex`, prop:collar, equation(5.3), lines539–549.
DAG: `collar-hopf-square-pairing-equations`; sole worker W2.
Use the EXISTING full square column family and genuine CLM inverse.
No desired metric identities or formal derivative axioms are inputs.
-/

noncomputable section
open WithLp

namespace GlobalEmbedding.Paper

/-- The literal square pairing with the SAME actual r, first and sorted-second
columns. The already defined finite synthesis operator's adjoint is exactly
the tuple of their real inner products, with the existing square data index. -/
def hopfCollarSquarePairing {m N : ℕ} (C : Fin m → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) :
    EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Unit ⊕ BalancedPairingIndex m) :=
  (freeColumnOperator (hopfCollarSquareColumns C G r x)).adjoint

/-- The literal RHS of (5.3), in that SAME original square column order.
The r row and all first rows are zero; each sorted-second row is the true
inner product of the corresponding original Hopf derivatives of actual G_r. -/
def hopfCollarSquareForcing {m N : ℕ} (C : Fin m → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) :
    EuclideanSpace ℝ (Unit ⊕ BalancedPairingIndex m) :=
  toLp 2 (fun k ↦ match k with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr ij) => inner ℝ
      (freeHopfDeriv C ij.val.1 (hopfCollarRDeriv G r) x)
      (freeHopfDeriv C ij.val.2 (hopfCollarRDeriv G r) x))

/-- Every actual square row is precisely its original real pairing.
Test the genuine synthesis adjoint against the actual Euclidean unit vector;
the existing synthesis formula selects the SAME original column. -/
theorem hopfCollarSquarePairing_apply {m N : ℕ} (C : Fin m → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) (w : EuclideanSpace ℝ (Fin N))
    (k : Unit ⊕ BalancedPairingIndex m) :
    hopfCollarSquarePairing C G r x w k = inner ℝ w (hopfCollarSquareColumns C G r x k) := by
  let A := freeColumnOperator (hopfCollarSquareColumns C G r x)
  have h := A.adjoint_inner_left (EuclideanSpace.single k 1) w
  have hcol : A (EuclideanSpace.single k 1) = hopfCollarSquareColumns C G r x k := by
    simp [A, freeColumnOperator_apply, PiLp.single_apply]
  rw [hcol, EuclideanSpace.inner_single_right] at h
  simpa only [hopfCollarSquarePairing, A, starRingEnd_apply, star_trivial, one_mul] using h

/-- The actual inverse PDE (5.3) implies each literal paired acceleration row.
Apply the actual invertible square pairing, cancel its existing total inverse,
then evaluate the original r/first/sorted-second coordinates. The acceleration
is the actual real derivative of the already defined G_r, not formal jet data.
No speed, mixed or old-Gram metric identity is an assumption. -/
theorem hopfCollar_square_inverse_pde_equations {m N : ℕ} (C : Fin m → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C)
    (hT : (hopfCollarSquarePairing C G r x).IsInvertible)
    (hPDE : deriv (fun s ↦ hopfCollarRDeriv G s x) r =
      (hopfCollarSquarePairing C G r x).inverse (hopfCollarSquareForcing C G r x)) :
    inner ℝ (deriv (fun s ↦ hopfCollarRDeriv G s x) r) (hopfCollarRDeriv G r x) = 0 ∧
    (∀ i, inner ℝ (deriv (fun s ↦ hopfCollarRDeriv G s x) r)
      (freeHopfDeriv C i (fun y ↦ G (r, y)) x) = 0) ∧
    (∀ ij : {p : Fin m × Fin m // p.1 ≤ p.2},
      inner ℝ (deriv (fun s ↦ hopfCollarRDeriv G s x) r)
        (freeHopfDeriv C ij.val.1 (freeHopfDeriv C ij.val.2 (fun y ↦ G (r, y))) x) =
      inner ℝ (freeHopfDeriv C ij.val.1 (hopfCollarRDeriv G r) x)
        (freeHopfDeriv C ij.val.2 (hopfCollarRDeriv G r) x)) := by
  have heq : hopfCollarSquarePairing C G r x
      (deriv (fun s ↦ hopfCollarRDeriv G s x) r) = hopfCollarSquareForcing C G r x := by
    rw [hPDE]
    exact hT.self_apply_inverse _
  have hrow (k : Unit ⊕ BalancedPairingIndex m) := congrArg (fun u ↦ u k) heq
  simp only [hopfCollarSquarePairing_apply] at hrow
  refine ⟨hrow (Sum.inl ()), fun i ↦ hrow (Sum.inr (Sum.inl i)), ?_⟩
  intro ij
  exact hrow (Sum.inr (Sum.inr ij))

end GlobalEmbedding.Paper
