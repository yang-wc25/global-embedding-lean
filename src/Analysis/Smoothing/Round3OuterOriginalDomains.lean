import Smoothing.Round3OuterDomains

/-! Exact original source-first ABI on the full receiving chart targets. -/
open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section
variable {n d q pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance round3OuterOriginalDomainsChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round3OuterOriginalDomainsIsManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)
local notation "cp" => EuclideanSpace.equiv (Fin d) ℝ
local notation "cs" => EuclideanSpace.equiv (Fin n) ℝ
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ


def round3OuterOriginalEvaluation
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (W : Set P) (i : Fin A.count × Fin pcount) : Set (Fin (n+d) → ℝ) :=
  incrementsOriginalDifferentiation A B.chart i ∩
    {y | (incrementsOriginalJointPoint A B.chart i y).1 ∈ W}

theorem round3OuterOriginalEvaluation_subset
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (W : Set P) (i : Fin A.count × Fin pcount) :
    round3OuterOriginalEvaluation A B W i ⊆ incrementsOriginalDifferentiation A B.chart i :=
  fun _ hy => hy.1

theorem round3OuterOriginalEvaluation_univ
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep) :
    round3OuterOriginalEvaluation A B univ = incrementsOriginalDifferentiation A B.chart := by
  funext i
  ext y
  simp only [round3OuterOriginalEvaluation, mem_inter_iff, mem_setOf_eq, mem_univ, and_true]

theorem round3OuterNative_model_evaluation
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (W : Set P) (i : Fin A.count × Fin pcount) :
    round3OuterModelEvaluation (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
      (Prod.fst ⁻¹' W) i = round3OuterOriginalEvaluation A B W i := by
  change ((parameterTensorModelEquiv n d).symm ⁻¹'
    ((parameterLocalProductFamily A B).chart i).target) ∩
    {y | (incrementsOriginalJointPoint A B.chart i y).1 ∈ W} = _
  rw [parameterLocalProduct_targets]
  rfl

theorem round3Outer_parameterLocalMap_weighted_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey) (W : Set P) (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (parameterLocalMapModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (cy ∘ u))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d))
      (round3OuterModelEvaluation (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (Prod.fst ⁻¹' W)) =
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (round3OuterOriginalEvaluation A B W) := by
  rw [parameterLocalMap_weighted_eq_original]
  congr 1
  exact funext (round3OuterNative_model_evaluation A B W)

theorem round3Outer_parameterLocalMap_weighted_allTargets_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (u : P × M → Ey) (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (parameterLocalMapModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (cy ∘ u))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)) =
    paperAtlasWeighted base m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (incrementsOriginalDifferentiation A B.chart) := by
  rw [parameterLocalMap_weighted_eq_original]
  congr 1
  exact funext (parameterLocalProduct_targets A B)

theorem round3Outer_tensorLocalNative_weighted_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (W : Set P) (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (tensorLocalModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
        (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d))
      (round3OuterModelEvaluation (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d) (Prod.fst ⁻¹' W)) =
    paperAtlasWeighted base m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (round3OuterOriginalEvaluation A B W) := by
  rw [tensorLocalNative_weighted_eq_original A B hA H base m t _
    (round3OuterModelEvaluation_subset_target _ _ _)]
  congr 1
  exact funext (round3OuterNative_model_evaluation A B W)

theorem round3Outer_tensorLocalNative_weighted_allTargets_eq_original
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (base m : ℕ) (t : ℝ) :
    paperAtlasWeighted base m t
      (tensorLocalModelCoordinates (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)
        (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d))
      (tensorLocalModelTargets (parameterLocalProductFamily A B) (parameterTensorModelEquiv n d)) =
    paperAtlasWeighted base m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (incrementsOriginalDifferentiation A B.chart) := by
  rw [tensorLocalNative_weighted_eq_original A B hA H base m t _ (fun _ => Subset.rfl)]
  congr 1
  exact funext (parameterLocalProduct_targets A B)

#print axioms round3Outer_tensorLocalNative_weighted_eq_original
#print axioms round3Outer_parameterLocalMap_weighted_allTargets_eq_original
end
end GlobalEmbedding.Continuation
