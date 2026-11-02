import GlobalEmbedding.Paper.HopfCollarSquarePairing

/-!
# Actual invertible collar pairing gives independence of the original full columns

Source: `main.tex`, Proposition `prop:collar`, lines 539–550.
Only an actual native adjoint/injectivity specialization; no inverse construction is repeated.
-/

namespace GlobalEmbedding.Paper

/-- The SAME full actual square family is independent wherever its actual pairing is invertible.

Proof: the actual pairing is the actual column synthesis adjoint. Native invertibility
makes it surjective, so every data vector is its value at some z. If synthesis sends u,v
to the same vector, native adjoint duality gives equal inner products of u,v with every
data vector. Native inner extensionality gives u=v, and the accepted synthesis criterion
gives the literal original column independence. No dimension or generic inverse proof.
Source: retained square invertibility in prop:collar539–550. -/
theorem hopfCollar_square_columns_linearIndependent {m N : ℕ} (C : Fin m → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C)
    (hT : (hopfCollarSquarePairing C G r x).IsInvertible) :
    LinearIndependent ℝ (hopfCollarSquareColumns C G r x) := by
  apply (freeColumnOperator_injective_iff _).mp
  intro u v huv
  apply ext_inner_left ℝ
  intro w
  obtain ⟨z, hz⟩ := hT.surjective w
  rw [← hz]
  change inner ℝ ((freeColumnOperator (hopfCollarSquareColumns C G r x)).adjoint z) u =
    inner ℝ ((freeColumnOperator (hopfCollarSquareColumns C G r x)).adjoint z) v
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, huv]

end GlobalEmbedding.Paper
