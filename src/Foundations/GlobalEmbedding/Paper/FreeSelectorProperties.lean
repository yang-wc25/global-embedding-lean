import GlobalEmbedding.Paper.BalancedPairing
import GlobalEmbedding.Paper.PlanarPeriodOneCalculus

/-!
# The literal first and symmetric second columns of a free selector

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 216–220 and 421–428.
These lower-level definitions contain no asserted selector existence and no alternative
product carrier or column index. The derivatives are the literal orbit derivatives.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual ordered first/second index has precisely the source's arithmetic
cardinality. Apply the accepted symmetric-square count to the preceding real equivalence.
Source: s_a=a(a+1)/2 at line 108 and a+s_a at line 220. -/
theorem free_pairing_index_card_arithmetic (a : ℕ) :
    Fintype.card (BalancedPairingIndex a) = a + a * (a + 1) / 2 := by
  rw [balanced_pairing_index_card, free_symmetric_column_count]

/-- The whole ordered family of actual first and once-indexed symmetric second orbit
derivatives. `BalancedPairingIndex` is reused verbatim, with no omitted diagonal columns.
The second column `(i,j)` is literally R_i(R_j F), as in balanced pairing columns.
Source: setup:partial, line 220. -/
noncomputable def freeFlowColumns {M : Type*} {a N : ℕ}
    (R : Fin a → ℝ → M → M) (F : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    BalancedPairingIndex a → EuclideanSpace ℝ (Fin N)
  | Sum.inl i => orbitDeriv (R i) F x
  | Sum.inr ij => orbitDeriv (R ij.val.1) (orbitDeriv (R ij.val.2) F) x

/-- The full same-map properties in thm:free: native smoothness at every order, exact
partial Gram, all first and symmetric second columns independent everywhere, and the
same globally smooth unit vector perpendicular to every column. The final target uses
exactly a+s_a+1 target coordinates; the proved index count then makes this complement
a line. This predicate constructs neither the map nor its normal and assumes no inverse.
Source: thm:free, lines 421–428, and free-unit-line-complement's statement definition. -/
def FreeSelectorProperties {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] {a N : ℕ}
    (R : Fin a → ℝ → M → M) (F ν : M → EuclideanSpace ℝ (Fin N)) : Prop :=
  ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F ∧
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ ν ∧
    (∀ x, Matrix.gram ℝ (fun i ↦ orbitDeriv (R i) F x) = 1) ∧
    (∀ x, LinearIndependent ℝ (freeFlowColumns R F x)) ∧
    (∀ x, ‖ν x‖ = 1) ∧
    (∀ x j, inner ℝ (ν x) (freeFlowColumns R F x j) = 0)

#print axioms balanced_pairing_index_card
#print axioms free_pairing_index_card_arithmetic

end GlobalEmbedding.Paper
