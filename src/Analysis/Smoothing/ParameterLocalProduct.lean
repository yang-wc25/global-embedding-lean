import Smoothing.TensorLocalCharts
import Smoothing.ParameterTotalNorms

/-!
# Actual product chart families with no global parameter-cover premise

The original source atlas is retained. The parameter factor is a genuinely
possibly noncovering finite buffered family. The index is the frozen original
source-first pair, while the model is parameter x source. Every chart and
buffer is literal; no global BufferedAtlas is manufactured by restriction.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Ep Es P M : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [TopologicalSpace P] [TopologicalSpace M] {pcount : ℕ}

/-- Actual source-first indexed product of a source atlas and a local parameter family. -/
def parameterLocalProductFamily (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep) :
    TensorBufferedChartFamily (Fin A.count × Fin pcount) (P × M) (Ep × Es) where
  chart i := (B.chart i.2).prod (A.chart i.1)
  inner i := B.inner i.2 ×ˢ A.inner i.1
  inner_open i := (B.inner_open i.2).prod (A.inner_open i.1)
  inner_subset i x hx := ⟨B.inner_subset _ hx.1,A.inner_subset _ hx.2⟩
  buffer := min B.buffer A.buffer
  buffer_pos := lt_min B.buffer_pos A.buffer_pos
  buffered i x hx z hz := by
    change z.1 ∈ (B.chart i.2).target ∧ z.2 ∈ (A.chart i.1).target
    change dist z (B.chart i.2 x.1,A.chart i.1 x.2) < min B.buffer A.buffer at hz
    rw [Prod.dist_eq,max_lt_iff] at hz
    exact ⟨B.buffered _ x.1 hx.1 (hz.1.trans_le (min_le_left _ _)),
      A.buffered _ x.2 hx.2 (hz.2.trans_le (min_le_right _ _))⟩

/-- Only the requested parameter set needs a cover. -/
theorem parameterLocalProductFamily_cover_on (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep) (K : Set P)
    (hcover : ∀ p ∈ K, ∃ j, p ∈ B.inner j) :
    ∀ z : P × M, z.1 ∈ K → ∃ i, z ∈ (parameterLocalProductFamily A B).inner i := by
  intro z hz
  obtain ⟨j,hj⟩ := hcover z.1 hz
  obtain ⟨i,hi⟩ := A.cover z.2
  exact ⟨(i,j),hj,hi⟩

theorem parameterLocalProductFamily_inner (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep) (i : Fin A.count × Fin pcount) :
    tensorLocalInner (parameterLocalProductFamily A B) i =
      tensorLocalInner B i.2 ×ˢ bufferedInnerCoordinates A i.1 := by
  ext z
  change ((z.1 ∈ _ ∧ z.2 ∈ _) ∧ (_ ∈ _ ∧ _ ∈ _)) ↔
    ((z.1 ∈ _ ∧ _ ∈ _) ∧ (z.2 ∈ _ ∧ _ ∈ _))
  tauto

variable [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
    [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]
local instance parameterLocalProductChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance parameterLocalProductIsManifold : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M

theorem parameterLocalProductFamily_chart_mem (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep) (hA : IsSmoothBufferedAtlas A)
    (hB : ∀ j, B.chart j ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (i : Fin A.count × Fin pcount) :
    (parameterLocalProductFamily A B).chart i ∈ maximalAtlas 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  change (B.chart i.2).prod (A.chart i.1) ∈ _
  rw [modelWithCornersSelf_prod]
  exact IsManifold.mem_maximalAtlas_prod (hB i.2) (hA.chart_mem i.1)

end
end GlobalEmbedding.Continuation

namespace GlobalEmbedding.Continuation
noncomputable section
variable {n d pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))

/-- Exact original joint point without requiring a global parameter atlas. -/
theorem parameterLocalProduct_jointPoint (i : Fin A.count × Fin pcount) (y : Fin (n+d) → ℝ) :
    ((parameterLocalProductFamily A B).chart i).symm ((parameterTensorModelEquiv n d).symm y) =
      incrementsOriginalJointPoint A B.chart i y := rfl

theorem parameterLocalProduct_targets (i : Fin A.count × Fin pcount) :
    (parameterTensorModelEquiv n d).symm ⁻¹' ((parameterLocalProductFamily A B).chart i).target =
      incrementsOriginalDifferentiation A B.chart i := by
  ext y
  exact and_comm

#print axioms parameterLocalProductFamily_chart_mem
#print axioms parameterLocalProduct_jointPoint
#print axioms parameterLocalProductFamily_cover_on
end
end GlobalEmbedding.Continuation
