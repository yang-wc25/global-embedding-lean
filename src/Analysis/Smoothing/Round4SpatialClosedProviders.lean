import Smoothing.Round4ClosedParameterAtlas

/-! Exact reindexing of all actual providers; no chart count enters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {n d pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
private local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

theorem round4ClosedParameter_providers
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i)
    (chi : Fin A.count × Fin pcount → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hsupp : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (hpart : ∀ z, ∑ i, chi i z ^ 2 = 1)
    (Bc T : ℕ → ℝ) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘
        ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k) :
    let B' := round4ClosedParameterAtlas B hcover
    let AB := parameterProductAtlas A B'
    let chi' := fun k => chi ((parameterTensorAtlasIndex A B').symm k)
    (∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi' i)) ∧
    (∀ i, tsupport (chi' i) ⊆ AB.inner i) ∧
    (∀ z, ∑ i, chi' i z ^ 2 = 1) ∧
    (∀ z, (activeCutoffIndices chi' z).card ≤ D) ∧
    (∀ p i k, ∀ y ∈ (AB.chart p).target,
      (AB.chart p).symm y ∈ tsupport (chi' i) →
      ‖iteratedFDeriv ℝ k (chi' i ∘ (AB.chart p).symm) y‖ ≤ Bc k) ∧
    (∀ p i k, 1 ≤ k → ∀ y ∈ (AB.chart p).target,
      (AB.chart p).symm y ∈ tsupport (chi' i) →
      ‖iteratedFDeriv ℝ k (AB.chart i ∘ (AB.chart p).symm) y‖ ≤ T k) := by
  let B' := round4ClosedParameterAtlas B hcover
  let e := parameterTensorAtlasIndex A B'
  refine ⟨fun i => hchi _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨a, rfl⟩ := e.surjective i
    simpa only [e, B', Equiv.symm_apply_apply, round4ClosedParameterProduct_inner] using hsupp a
  · intro z
    rw [← Equiv.sum_comp e]
    change (∑ i : Fin A.count × Fin pcount, chi (e.symm (e i)) z ^ 2) = 1
    simpa only [Equiv.symm_apply_apply] using hpart z
  · intro z
    rw [round4ActiveCutoff_reindex_card]
    exact hD z
  · intro p i k
    obtain ⟨a, rfl⟩ := e.surjective p
    obtain ⟨b, rfl⟩ := e.surjective i
    simpa only [e, B', Equiv.symm_apply_apply, round4ClosedParameterProduct_chart] using hweight a b k
  · intro p i k hk
    obtain ⟨a, rfl⟩ := e.surjective p
    obtain ⟨b, rfl⟩ := e.surjective i
    simpa only [e, B', Equiv.symm_apply_apply, round4ClosedParameterProduct_chart] using htransition a b k hk

#print axioms round4ClosedParameter_providers
end GlobalEmbedding.Continuation
