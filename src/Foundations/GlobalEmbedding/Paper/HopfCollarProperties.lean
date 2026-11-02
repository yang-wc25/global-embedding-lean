import GlobalEmbedding.Paper.FreeHopfProductNative
import GlobalEmbedding.Paper.FreeSelectorProperties

/-!
# Native joint analytic collar properties on the original Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, setup:partial,
lines216–220, and prop:collar, lines508–515.
DAG: `collar-native-properties`. Exclusive owner W6.
The real parameter is written first; the source is the ordinary swap of the paper's
whole product times its open real interval. No new manifold atlas or flow is introduced.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The literal partial derivative in the genuine real collar coordinate, with the
whole-product point fixed. This ordinary real derivative agrees with the native
coordinate derivative on every open collar where the joint map is analytic.
The map may have arbitrary values outside that open collar. Source: G_r in (5.1). -/
def hopfCollarRDeriv {m N : ℕ} {C : Fin m → ℕ}
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) : EuclideanSpace ℝ (Fin N) :=
  deriv (fun s : ℝ ↦ G (s, x)) r

/-- The full square column family: the one actual G_r column, followed by the
existing first and once-indexed symmetric second columns of the same r-slice.
The old derivatives use precisely the original period-one Hopf factor flows;
the existing sorted index includes every diagonal pair. Source: prop:collar,
lines513–515 and the square pairing map in lines539–546. -/
def hopfCollarSquareColumns {m N : ℕ} (C : Fin m → ℕ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (r : ℝ) (x : FreeHopfProduct C) : Unit ⊕ BalancedPairingIndex m →
      EuclideanSpace ℝ (Fin N) :=
  Sum.elim (fun _ ↦ hopfCollarRDeriv G r x)
    (freeFlowColumns (freeHopfProductFlow C) (fun y ↦ G (r, y)) x)

/-- All original collar conclusions for one fixed map and one common open radius.
Analyticity is jointly native real analytic, at Mathlib's actual order omega, in
all source chart coordinates and the real parameter. It is asserted on the entire
whole-product collar, not only on Hopf orbits or initial jets. At every interval
point the same map has old Gram I, all old/r cross terms zero, squared r-speed one,
and the complete square family independent. The target supplies positive radius
and the exact original dimension; no replacement dimension or column count is used.
Source: prop:collar, lines508–515. -/
def AnalyticHopfCollarProperties {m N : ℕ} (C : Fin m → ℕ)
    [∀ i, Fact (0 < C i)] (r0 : ℝ)
    (G : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N)) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω
    G (Set.Ioo (-r0) r0 ×ˢ Set.univ) ∧
  ∀ r ∈ Set.Ioo (-r0) r0, ∀ x : FreeHopfProduct C,
    Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (fun y ↦ G (r, y)) x) = 1 ∧
    (∀ i, inner ℝ (freeHopfDeriv C i (fun y ↦ G (r, y)) x)
      (hopfCollarRDeriv G r x) = 0) ∧
    ‖hopfCollarRDeriv G r x‖ ^ 2 = 1 ∧
    LinearIndependent ℝ (hopfCollarSquareColumns C G r x)

#print axioms hopfCollarRDeriv
#print axioms hopfCollarSquareColumns
#print axioms AnalyticHopfCollarProperties

end GlobalEmbedding.Paper
