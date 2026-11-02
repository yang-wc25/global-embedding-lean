import Smoothing.ParameterLocalMap

/-!
# Actual local parameter partitions and the same global map operator

Only the original compact parameter set K needs raw unit plateaus. A genuine
open neighborhood U of K carries the exact product square partition. Globally
smooth normalized cutoffs retain their original supports and active degree.
The map's actual error identity therefore holds as a germ on U x M, without
asserting that finitely many parameter charts cover all of P.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set Filter MeasureTheory Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Ep Es P M : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [TopologicalSpace P] [TopologicalSpace M] {pcount : ℕ}

def parameterLocalProductCutoff (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (i : Fin A.count × Fin pcount) (z : P × M) : ℝ :=
  chiP i.2 z.1 * chiS i.1 z.2

theorem parameterLocalProductCutoff_tsupport_subset (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (i : Fin A.count × Fin pcount) :
    tsupport (parameterLocalProductCutoff A B chiS chiP i) ⊆
      tsupport (chiP i.2) ×ˢ tsupport (chiS i.1) := by
  intro z hz
  exact ⟨tsupport_comp_subset_preimage _ continuous_fst (tsupport_mul_subset_left hz),
    tsupport_comp_subset_preimage _ continuous_snd (tsupport_mul_subset_right hz)⟩

theorem parameterLocalProductCutoff_support (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (hS : ∀ i, tsupport (chiS i) ⊆ A.inner i) (hP : ∀ j, tsupport (chiP j) ⊆ B.inner j) :
    ∀ i, tsupport (parameterLocalProductCutoff A B chiS chiP i) ⊆
      (parameterLocalProductFamily A B).inner i := by
  intro i z hz
  have h := parameterLocalProductCutoff_tsupport_subset A B chiS chiP i hz
  exact ⟨hP _ h.1,hS _ h.2⟩

theorem parameterLocalProductCutoff_square_sum_on (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (hS : ∀ x, ∑ i, chiS i x ^ 2 = 1) {U : Set P}
    (hP : ∀ p ∈ U, ∑ j, chiP j p ^ 2 = 1) :
    ∀ z : P × M, z.1 ∈ U → ∑ i, parameterLocalProductCutoff A B chiS chiP i z ^ 2 = 1 := by
  intro z hz
  simp only [parameterLocalProductCutoff,mul_pow,Fintype.sum_prod_type,← Finset.sum_mul,hP _ hz,
    one_mul,hS]

theorem parameterLocalProductCutoff_card_le (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (Ds Dp : ℕ) (hS : ∀ x, (activeCutoffIndices chiS x).card ≤ Ds)
    (hP : ∀ p, (activeCutoffIndices chiP p).card ≤ Dp) :
    ∀ z, (activeCutoffIndices (parameterLocalProductCutoff A B chiS chiP) z).card ≤ Ds*Dp := by
  classical
  intro z
  have hsub : activeCutoffIndices (parameterLocalProductCutoff A B chiS chiP) z ⊆
      (activeCutoffIndices chiS z.2) ×ˢ (activeCutoffIndices chiP z.1) := by
    intro i hi
    have hs := parameterLocalProductCutoff_tsupport_subset A B chiS chiP i
      ((mem_activeCutoffIndices _ z i).mp hi)
    exact Finset.mem_product.mpr ⟨(mem_activeCutoffIndices _ _ _).mpr hs.2,
      (mem_activeCutoffIndices _ _ _).mpr hs.1⟩
  exact (Finset.card_le_card hsub).trans (by
    rw [Finset.card_product]
    exact Nat.mul_le_mul (hS z.2) (hP z.1))

variable [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
    [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]
local instance parameterLocalCutoffsChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance parameterLocalCutoffsIsManifold : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

theorem parameterLocalProductCutoff_contMDiff (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin pcount → P → ℝ)
    (hS : ∀ i, ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, ℝ) ∞ (chiS i))
    (hP : ∀ j, ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, ℝ) ∞ (chiP j)) :
    ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (parameterLocalProductCutoff A B chiS chiP i) := by
  intro i
  rw [modelWithCornersSelf_prod]
  exact ((hP i.2).comp contMDiff_fst).mul ((hS i.1).comp contMDiff_snd)

/-- Raw parameter plateaus only on K yield the actual product partition on
an open neighborhood; original supports and multiplicity are preserved. -/
theorem parameterLocalProductCutoff_preparation_near
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (chiS : Fin A.count → M → ℝ) (rawP : Fin pcount → P → ℝ)
    (hS : ∀ i, ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, ℝ) ∞ (chiS i))
    (hP : ∀ j, ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, ℝ) ∞ (rawP j))
    (hSpart : ∀ x, ∑ i, chiS i x ^ 2 = 1)
    (hSsupp : ∀ i, tsupport (chiS i) ⊆ A.inner i)
    (hPsupp : ∀ j, tsupport (rawP j) ⊆ B.inner j)
    (Ds Dp : ℕ) (hSD : ∀ x, (activeCutoffIndices chiS x).card ≤ Ds)
    (hPD : ∀ p, (activeCutoffIndices rawP p).card ≤ Dp)
    (K : Set P) (hcover : ∀ p ∈ K, ∃ j, rawP j p = 1) :
    let chi := parameterLocalProductCutoff A B chiS (tensorLocalNormalizedCutoff rawP)
    ∃ U : Set P, IsOpen U ∧ K ⊆ U ∧
      (∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ z : P × M, z.1 ∈ U → ∑ i, chi i z ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i) ∧
      (∀ z, (activeCutoffIndices chi z).card ≤ Ds*Dp) := by
  obtain ⟨U,hU,hKU,hpart⟩ := tensorLocalNormalizedCutoff_partition_near rawP hP K hcover
  refine ⟨U,hU,hKU,parameterLocalProductCutoff_contMDiff A B chiS _ hS
    (tensorLocalNormalizedCutoff_contMDiff rawP hP),?_,?_,?_⟩
  · exact parameterLocalProductCutoff_square_sum_on A B chiS _ hSpart hpart
  · exact parameterLocalProductCutoff_support A B chiS _ hSsupp
      (fun j => (tensorLocalNormalizedCutoff_tsupport_subset rawP j).trans (hPsupp j))
  · exact parameterLocalProductCutoff_card_le A B chiS _ Ds Dp hSD
      (fun p => (tensorLocalNormalizedCutoff_card_le rawP p).trans (hPD p))

#print axioms parameterLocalProductCutoff_preparation_near
end
end GlobalEmbedding.Continuation
