import Smoothing.TensorNativeTransitions
import GlobalEmbedding.Offline.CutoffChartTransfer
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Smoothing providers from the actual fixed buffered preparation

Setup 6 supplies the actual buffered charts, pre-cutoffs and enlarged-support
intersection degree. This file derives the normalized square partition,
actual support multiplicity, and all receiving-chart cutoff derivative bounds.
The constants are chosen before the atlas or its total chart count.
It does not manufacture uniform chart geometry on an arbitrary manifold.
-/

open Module Manifold IsManifold GlobalEmbedding.Paper Function Set Filter
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

section Degree

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- The genuine enlarged-support intersection graph. -/
def tensorEnlargedSupportGraph (W : ι → Set X) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (W i ∩ W j).Nonempty
  symm := by
    constructor
    rintro i j ⟨hne, x, hxi, hxj⟩
    exact ⟨hne.symm, x, hxj, hxi⟩
  loopless := ⟨fun i h => h.1 rfl⟩

def tensorEnlargedSupportDegree (W : ι → Set X) (i : ι) : ℕ := by
  classical
  exact (tensorEnlargedSupportGraph W).degree i

/-- The original degree bound directly controls actual topological supports
through a point by D+1, including empty families and no coloring premise. -/
theorem activeCutoffIndices_card_le_enlarged_degree
    (W : ι → Set X) (f : ι → X → ℝ) (hsupp : ∀ i, tsupport (f i) ⊆ W i)
    (D : ℕ) (hdegree : ∀ i, tensorEnlargedSupportDegree W i ≤ D) (x : X) :
    (activeCutoffIndices f x).card ≤ D + 1 := by
  classical
  let S := activeCutoffIndices f x
  by_cases hS : S = ∅
  · simp only [show activeCutoffIndices f x = ∅ from hS, Finset.card_empty]
    omega
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  let G := tensorEnlargedSupportGraph W
  have hsub : S ⊆ insert i (G.neighborFinset i) := by
    intro j hj
    by_cases hji : j = i
    · exact Finset.mem_insert.mpr (Or.inl hji)
    · apply Finset.mem_insert.mpr
      right
      apply (G.mem_neighborFinset i j).mpr
      exact ⟨Ne.symm hji, x, hsupp i ((mem_activeCutoffIndices f x i).mp hi),
        hsupp j ((mem_activeCutoffIndices f x j).mp hj)⟩
  calc
    S.card ≤ (insert i (G.neighborFinset i)).card := Finset.card_le_card hsub
    _ ≤ (G.neighborFinset i).card + 1 := Finset.card_insert_le _ _
    _ ≤ D + 1 := Nat.add_le_add_right (hdegree i) 1

/-- Normalization retains the actual enlarged-support multiplicity. -/
theorem squareNormalizedCutoff_card_le_enlarged_degree
    (W : ι → Set X) (f : ι → X → ℝ) (hsupp : ∀ i, tsupport (f i) ⊆ W i)
    (D : ℕ) (hdegree : ∀ i, tensorEnlargedSupportDegree W i ≤ D) (x : X) :
    (activeCutoffIndices (squareNormalizedCutoff f) x).card ≤ D + 1 :=
  activeCutoffIndices_card_le_enlarged_degree W (squareNormalizedCutoff f)
    (fun i => (squareNormalizedCutoff_tsupport_subset f i).trans (hsupp i)) D hdegree x

end Degree

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The existing fixed raw buffered preparation supplies all smoothing cutoff
premises. No mixed-chart cutoff bound, square partition, or multiplicity bound
is assumed: each is proved for the literal normalized functions.
The remaining premises are exactly raw bump preparation and genuine uniform
chart-transition bounds on active enlarged overlaps. -/
theorem exists_uniform_tensor_cutoff_provider
    (B₀ T : ℕ → ℝ) (hB₀ : ∀ j, 0 ≤ B₀ j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A),
      ∀ (f : Fin A.count → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f i)) →
      (∀ x, ∃ i, f i x = 1) →
      (∀ i, tsupport (f i) ⊆ A.inner i) →
      ∀ W : Fin A.count → Set M,
      (∀ i, tsupport (f i) ⊆ W i) →
      (∀ i, tensorEnlargedSupportDegree W i ≤ D) →
      (∀ i j, ∀ y ∈ (A.chart i).target,
        ‖iteratedFDeriv ℝ j (f i ∘ (A.chart i).symm) y‖ ≤ B₀ j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ tsupport (f i) →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ T j) →
      let chi := squareNormalizedCutoff f
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ x, ∑ i, chi i x ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ A.inner i) ∧
      (∀ x, (activeCutoffIndices chi x).card ≤ D + 1) ∧
      (∀ p i j, ∀ y ∈ bufferedInnerCoordinates A p,
        (A.chart p).symm y ∈ tsupport (chi i) →
        ‖iteratedFDeriv ℝ j (chi i ∘ (A.chart p).symm) y‖ ≤ B j) := by
  obtain ⟨C, hC, hnormalize⟩ := exists_normalizedCutoff_bounds_from_chartProviders
    (E := E) (M := M) B₀ T hB₀ hT (D + 1)
  obtain ⟨B, hB, htransfer⟩ := exists_actualChart_cutoff_transfer_bounds
    (E := E) (M := M) C T hC hT
  refine ⟨B, hB, ?_⟩
  intro A hA f hf hcover hinner W hsupp hdegree hown htrans
  obtain ⟨hchi, hpartition, _, hsupport, hownChi⟩ := hnormalize (Fin A.count) 1 le_rfl f hf hcover
    (activeCutoffIndices_card_le_enlarged_degree W f hsupp D hdegree)
    A.chart hA.chart_mem (fun i => (hinner i).trans (A.inner_subset i))
    (by simpa only [one_pow, mul_one] using hown) htrans
  refine ⟨hchi, hpartition, fun i => (hsupport i).trans (hinner i),
    squareNormalizedCutoff_card_le_enlarged_degree W f hsupp D hdegree, ?_⟩
  intro p i j y hy hi
  have hiRaw := hsupport i hi
  have hiS : (A.chart p).symm y ∈ (A.chart i).source := A.inner_subset i (hinner i hiRaw)
  have h := htransfer 1 le_rfl (squareNormalizedCutoff f i) (hchi i) (A.chart p) (A.chart i)
    (hA.chart_mem p) (hA.chart_mem i) y ⟨hy.1, hiS⟩
    (fun k => hownChi i k _ ((A.chart i).map_source hiS))
    (fun k hk => htrans p i k hk y hy.1 hiRaw) j
  simpa only [one_pow, mul_one] using h

end

end GlobalEmbedding.Offline
