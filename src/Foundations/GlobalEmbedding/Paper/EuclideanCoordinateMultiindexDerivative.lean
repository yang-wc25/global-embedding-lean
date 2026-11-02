import GlobalEmbedding.Paper.EuclideanCoordinateWordDerivative
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Multiset.Sort

/-!
# Genuine Finsupp multiindex partial derivatives on actual Euclidean lifts

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1), lines 388–399.
DAG node: `euclidean-coordinate-multiindex-derivative`.
-/

namespace GlobalEmbedding.Paper

/-- The genuine coordinate partial derivative of a multiindex, in increasing coordinate order.

The actual Finsupp multiindex gives its exact multiset of coordinate multiplicities. Sort
that multiset in the original Fin a order and apply the actual iterated coordinate derivative.
Exact degree/multiplicity and C2 order-independence are proved separately. Source: (4.1). -/
noncomputable def euclideanCoordinateMultiindexDerivative {a N : ℕ} (β : Fin a →₀ ℕ)
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N) :=
  euclideanCoordinateWordDerivative (β.toMultiset.sort (· ≤ ·)) f

#print axioms euclideanCoordinateMultiindexDerivative

end GlobalEmbedding.Paper
