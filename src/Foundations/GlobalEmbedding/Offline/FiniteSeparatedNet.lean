import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Pairwise.Lattice

/-!
# Finite separated nets with the exact open covering radius

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`prop:initialization`, line 801; DAG leaf
`initialization-colored-cutoffs-separated-net-finite-maximal-net`.

The required inequalities are separation `δ ≤ edist` and covering
`edist < δ`, at the SAME radius. Mathlib's `Metric.IsSeparated` instead
uses `δ < edist`, while its `Metric.IsCover` uses `edist ≤ δ`. Consequently
the existing maximal-separated-set theorem cannot be substituted verbatim.
We use Mathlib's Zorn and total-boundedness primitives with the exact
required relation. Extended distances are retained throughout, so points
in different Riemannian components need not have finite distance.
-/

open Set Metric
open scoped ENNReal

namespace GlobalEmbedding.Offline

variable {X : Type*} [PseudoEMetricSpace X]

/-- A positive weakly separated subset of a totally bounded set is finite.

Cover the ambient set by finitely many open `δ/2` balls. The triangle
inequality shows that each ball meets the separated subset at most once;
the subset is therefore contained in a finite union of singleton sets.
This also covers empty sets and genuinely infinite extended distances. -/
theorem finite_of_totallyBounded_weakly_separated
    {K P : Set X} (hK : TotallyBounded K) (hPK : P ⊆ K)
    {δ : ℝ≥0∞} (hδ : 0 < δ)
    (hsep : P.Pairwise (fun x y ↦ δ ≤ edist x y)) : P.Finite := by
  have hhalf : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨C, hCfinite, hcover⟩ := EMetric.totallyBounded_iff.mp hK (δ / 2) hhalf
  have hlocal (z : X) : (P ∩ Metric.eball z (δ / 2)).Subsingleton := by
    intro x hx y hy
    by_contra hne
    have hxy : edist x y < δ := by
      calc
        edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
        _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hx.2 (by
          simpa only [Metric.mem_eball, edist_comm] using hy.2)
        _ = δ := ENNReal.add_halves δ
    exact (hsep hx.1 hy.1 hne).not_gt hxy
  apply (hCfinite.biUnion (fun z _hz ↦ (hlocal z).finite)).subset
  intro x hx
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hcover (hPK hx))
  exact Set.mem_iUnion₂.mpr ⟨z, hz, hx, hxz⟩

/-- A totally bounded set has a finite weakly separated net whose OPEN
balls of the exact same radius cover it.

Zorn gives a maximal subset with pairwise distance at least `δ`; chain
unions preserve this condition. The preceding lemma makes it finite. If
a point were at distance at least `δ` from every center, adjoining it would
contradict maximality. The positive radius ensures that an existing center
already covers itself. No connectedness or nonemptiness is assumed. -/
theorem exists_finite_weakly_separated_open_net
    {K : Set X} (hK : TotallyBounded K) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ P : Set X, P ⊆ K ∧ P.Finite ∧
      P.Pairwise (fun x y ↦ δ ≤ edist x y) ∧
      ∀ x ∈ K, ∃ p ∈ P, edist x p < δ := by
  let S : Set (Set X) := {P | P ⊆ K ∧ P.Pairwise (fun x y ↦ δ ≤ edist x y)}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hline
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
    · exact Set.sUnion_subset fun s hs ↦ (hc hs).1
    · exact (Set.pairwise_sUnion hline.directedOn).2 fun s hs ↦ (hc hs).2
  obtain ⟨P, hmax⟩ := zorn_subset S hchain
  refine ⟨P, hmax.1.1, finite_of_totallyBounded_weakly_separated hK hmax.1.1 hδ hmax.1.2,
    hmax.1.2, ?_⟩
  intro x hx
  by_contra hnot
  push Not at hnot
  have hsub : insert x P ⊆ K := Set.insert_subset hx hmax.1.1
  have hsep : (insert x P).Pairwise (fun a b ↦ δ ≤ edist a b) := by
    apply hmax.1.2.insert
    intro p hp _hne
    exact ⟨hnot p hp, by simpa only [edist_comm] using hnot p hp⟩
  have hxP : x ∈ P := hmax.2 ⟨hsub, hsep⟩ (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact (hnot x hxP).not_gt (by simpa using hδ)

/-- Compact emetric spaces admit the exact-radius finite nets used by the
initialization argument, directly across all components. -/
theorem exists_compact_finite_separated_open_net [CompactSpace X]
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ P : Set X, P.Finite ∧
      P.Pairwise (fun x y ↦ δ ≤ edist x y) ∧
      ∀ x : X, ∃ p ∈ P, edist x p < δ := by
  obtain ⟨P, _hsub, hfinite, hsep, hcover⟩ :=
    exists_finite_weakly_separated_open_net
      (isCompact_univ : IsCompact (Set.univ : Set X)).totallyBounded hδ
  exact ⟨P, hfinite, hsep, fun x ↦ hcover x (Set.mem_univ x)⟩

#print axioms finite_of_totallyBounded_weakly_separated
#print axioms exists_finite_weakly_separated_open_net
#print axioms exists_compact_finite_separated_open_net

end GlobalEmbedding.Offline
