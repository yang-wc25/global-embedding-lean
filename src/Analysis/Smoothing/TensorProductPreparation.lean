import Smoothing.TensorProductJets
import Smoothing.TensorSetupProviders

/-!
# The literal product of the original prepared cutoff families

This supplies the true product atlas data used simultaneously by map and tensor
smoothing. The support bound is the product of the original local overlap
bounds, never the number of product charts. The actual normalized functions
may be obtained from `exists_uniform_tensor_cutoff_provider` in each factor.
-/

open Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Ep Es P M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [TopologicalSpace P] [TopologicalSpace M]

/-- One fixed actual cutoff on each original product chart. -/
def tensorProductCutoff (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (i : Fin (parameterProductAtlas A B).count) (z : P × M) : ℝ :=
  chiP (parameterProductIndex A B i).1 z.1 * chiS (parameterProductIndex A B i).2 z.2

/-- The actual product support lies in the product of actual factor supports. -/
theorem tensorProductCutoff_tsupport_subset (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (i : Fin (parameterProductAtlas A B).count) :
    tsupport (tensorProductCutoff A B chiS chiP i) ⊆
      tsupport (chiP (parameterProductIndex A B i).1) ×ˢ
        tsupport (chiS (parameterProductIndex A B i).2) := by
  intro z hz
  exact ⟨tsupport_comp_subset_preimage _ continuous_fst (tsupport_mul_subset_left hz),
    tsupport_comp_subset_preimage _ continuous_snd (tsupport_mul_subset_right hz)⟩

theorem tensorProductCutoff_support (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (hS : ∀ i, tsupport (chiS i) ⊆ A.inner i)
    (hP : ∀ i, tsupport (chiP i) ⊆ B.inner i) :
    ∀ i, tsupport (tensorProductCutoff A B chiS chiP i) ⊆
      (parameterProductAtlas A B).inner i := by
  intro i z hz
  have h := tensorProductCutoff_tsupport_subset A B chiS chiP i hz
  exact ⟨hP _ h.1, hS _ h.2⟩

/-- The product of the TWO original square partitions is itself exactly a
square partition. No normalization depending on the number of charts is used. -/
theorem tensorProductCutoff_square_sum (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (hS : ∀ x, ∑ i, chiS i x ^ 2 = 1) (hP : ∀ p, ∑ i, chiP i p ^ 2 = 1) :
    ∀ z, ∑ i, tensorProductCutoff A B chiS chiP i z ^ 2 = 1 := by
  intro z
  change (∑ i : Fin (B.count * A.count),
    (chiP (parameterProductIndex A B i).1 z.1 * chiS (parameterProductIndex A B i).2 z.2) ^ 2) = 1
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [parameterProductIndex, Equiv.symm_apply_apply, mul_pow]
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, hS, mul_one, hP]

/-- Actual active product supports are contained in the product of the
active factor supports. The resulting multiplicity is Dp * Ds. -/
theorem tensorProductCutoff_card_le (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (Ds Dp : ℕ) (hS : ∀ x, (activeCutoffIndices chiS x).card ≤ Ds)
    (hP : ∀ p, (activeCutoffIndices chiP p).card ≤ Dp) :
    ∀ z, (activeCutoffIndices (tensorProductCutoff A B chiS chiP) z).card ≤ Dp * Ds := by
  classical
  intro z
  let U := (activeCutoffIndices chiP z.1) ×ˢ (activeCutoffIndices chiS z.2)
  have hsub : activeCutoffIndices (tensorProductCutoff A B chiS chiP) z ⊆
      U.image finProdFinEquiv := by
    intro i hi
    have hz := tensorProductCutoff_tsupport_subset A B chiS chiP i
      ((mem_activeCutoffIndices _ z i).mp hi)
    apply Finset.mem_image.mpr
    refine ⟨parameterProductIndex A B i, Finset.mem_product.mpr ⟨?_, ?_⟩,
      finProdFinEquiv.apply_symm_apply i⟩
    · exact (mem_activeCutoffIndices chiP z.1 _).mpr hz.1
    · exact (mem_activeCutoffIndices chiS z.2 _).mpr hz.2
  calc
    _ ≤ (U.image finProdFinEquiv).card := Finset.card_le_card hsub
    _ ≤ U.card := Finset.card_image_le
    _ = (activeCutoffIndices chiP z.1).card * (activeCutoffIndices chiS z.2).card :=
      Finset.card_product _ _
    _ ≤ Dp * Ds := Nat.mul_le_mul (hP z.1) (hS z.2)

/-- Inner coordinate domains are literally products of the original domains. -/
theorem tensorProductInnerCoordinates (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (i : Fin (parameterProductAtlas A B).count) :
    bufferedInnerCoordinates (parameterProductAtlas A B) i =
      bufferedInnerCoordinates B (parameterProductIndex A B i).1 ×ˢ
        bufferedInnerCoordinates A (parameterProductIndex A B i).2 := by
  ext z
  change ((z.1 ∈ _ ∧ z.2 ∈ _) ∧ (_ ∈ _ ∧ _ ∈ _)) ↔
    ((z.1 ∈ _ ∧ _ ∈ _) ∧ (z.2 ∈ _ ∧ _ ∈ _))
  tauto

variable [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

/-- The actual product cutoff is jointly smooth in the actual product atlas. -/
theorem tensorProductCutoff_contMDiff (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (hS : ∀ i, ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, ℝ) ∞ (chiS i))
    (hP : ∀ i, ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, ℝ) ∞ (chiP i)) :
    ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (tensorProductCutoff A B chiS chiP i) := by
  intro i
  rw [modelWithCornersSelf_prod]
  exact ((hP _).comp contMDiff_fst).mul ((hS _).comp contMDiff_snd)

/-- Separate receiving-chart cutoff bounds supply ALL joint derivatives of
the literal product cutoff. The new profile is the explicit Leibniz sum. -/
theorem tensorProductCutoff_jet_bound
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (hchiS : ∀ i, ContMDiff 𝓘(ℝ, Es) 𝓘(ℝ, ℝ) ∞ (chiS i))
    (hchiP : ∀ i, ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, ℝ) ∞ (chiP i))
    (BS BP : ℕ → ℝ) (hBS : ∀ j, 0 ≤ BS j) (hBP : ∀ j, 0 ≤ BP j)
    (hS : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chiS i) →
      ‖iteratedFDeriv ℝ k (chiS i ∘ (A.chart p).symm) y‖ ≤ BS k)
    (hP : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates B p,
      (B.chart p).symm y ∈ tsupport (chiP i) →
      ‖iteratedFDeriv ℝ k (chiP i ∘ (B.chart p).symm) y‖ ≤ BP k) :
    ∀ p i k, ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈
        tsupport (tensorProductCutoff A B chiS chiP i) →
      ‖iteratedFDeriv ℝ k
        (tensorProductCutoff A B chiS chiP i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤
        tensorProductJetConstant BP BS k := by
  intro p i k y hy hi
  rw [tensorProductInnerCoordinates] at hy
  have his := tensorProductCutoff_tsupport_subset A B chiS chiP i hi
  have hfs : ContDiffOn ℝ ∞
      (chiS (parameterProductIndex A B i).2 ∘ (A.chart (parameterProductIndex A B p).2).symm)
      (A.chart (parameterProductIndex A B p).2).target :=
    ((hchiS _).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem _))).contDiffOn
  have hfp : ContDiffOn ℝ ∞
      (chiP (parameterProductIndex A B i).1 ∘ (B.chart (parameterProductIndex A B p).1).symm)
      (B.chart (parameterProductIndex A B p).1).target :=
    ((hchiP _).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hB.chart_mem _))).contDiffOn
  exact tensor_product_scalar_jet_le
    (B.chart (parameterProductIndex A B p).1).open_target
    (A.chart (parameterProductIndex A B p).2).open_target hfp hfs hy.1.1 hy.2.1
    BP BS hBP hBS (fun j => hP _ _ j _ hy.1 his.1) (fun j => hS _ _ j _ hy.2 his.2) k

/-- The genuine product chart transition has uniformly bounded joint jets.
Only the original positive-order factor transition bounds are needed. -/
theorem tensorProductTransition_jet_bound
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (chiS : Fin A.count → M → ℝ) (chiP : Fin B.count → P → ℝ)
    (hSuppS : ∀ i, tsupport (chiS i) ⊆ A.inner i)
    (hSuppP : ∀ i, tsupport (chiP i) ⊆ B.inner i)
    (TS TP : ℕ → ℝ)
    (hS : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chiS i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS k)
    (hP : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates B p,
      (B.chart p).symm y ∈ tsupport (chiP i) →
      ‖iteratedFDeriv ℝ k (B.chart i ∘ (B.chart p).symm) y‖ ≤ TP k) :
    ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈
        tsupport (tensorProductCutoff A B chiS chiP i) →
      ‖iteratedFDeriv ℝ k
        ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤
        max (TP k) (TS k) := by
  intro p i k hk y hy hi
  rw [tensorProductInnerCoordinates] at hy
  have his := tensorProductCutoff_tsupport_subset A B chiS chiP i hi
  exact tensor_product_map_jet_le
    (bufferedChartOverlap_open B _ _) (bufferedChartOverlap_open A _ _)
    (bufferedTransition_contDiffOn B hB _ _) (bufferedTransition_contDiffOn A hA _ _)
    ⟨hy.1.1, hSuppP _ his.1⟩ ⟨hy.2.1, hSuppS _ his.2⟩ k (TP k) (TS k)
    (hP _ _ k hk _ hy.1 his.1) (hS _ _ k hk _ hy.2 his.2)

end
end GlobalEmbedding.Offline
