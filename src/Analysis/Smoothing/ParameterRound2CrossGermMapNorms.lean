import Smoothing.ParameterRound2CrossGermNorms

/-!
# Original weighted map norms produce the actual spatial jets used by Cross

The map is literally the native F in the original product chart. Full-joint
derivative bounds follow from the unchanged coordinate norm, with the stated
base shift. A true spatial derivative costs one shift, so base2 for the
smoothing error and base1 for the increment give the cross estimate directly.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2CrossGermMapNormChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CrossGermMapNormIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_original_metricCrossTerm_from_map_germ_norms
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (UI : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hUI : ∀ i, IsOpen (UI i))
    (hUIO : ∀ i, UI i ⊆ incrementsOriginalDifferentiation A B i)
    (hSUI : ∀ i, S i ⊆ UI i)
    (F U : P × M → Ey)
    (hF : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B F i) (UI i))
    (hU : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B U i) (UI i))
    (m : ℕ) (tau : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hFfinite : paperAtlasWeighted 2 m tau (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (hUfinite : paperAtlasWeighted 1 m tau (incrementsOriginalMapCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤) :
    let C := incrementsOriginalTensorCoordinates A B
      (fun p x => metricCrossTerm (I := 𝓘(ℝ, Es)) (fun z => F (p,z)) (fun z => U (p,z)) x)
    let WF := (paperAtlasWeighted 2 m tau (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal
    let WU := (paperAtlasWeighted 1 m tau (incrementsOriginalMapCoordinates A B U)
      (incrementsOriginalDifferentiation A B) S).toReal
    (∀ i, ContDiffOn ℝ ∞ (C i) (UI i)) ∧
    paperAtlasWeighted 0 m tau C (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 m tau C (incrementsOriginalDifferentiation A B) S).toReal ≤
        ((m+1) * linearModelFactor (parameterTensorModelEquiv n d).symm m * 2^(m+1) *
          parameterRound2_mapWeightedJetCost n d N 2 m *
          parameterRound2_mapWeightedJetCost n d N 1 m) * WF * WU := by
  dsimp only
  have h := parameterRound2_original_metricCrossTerm_germ_weighted_norm A B hA S hSO UI hUI hUIO hSUI F U hF hU m tau
    (parameterRound2_mapWeightedJetCost n d N 2 m *
      (paperAtlasWeighted 2 m tau (incrementsOriginalMapCoordinates A B F)
        (incrementsOriginalDifferentiation A B) S).toReal)
    (parameterRound2_mapWeightedJetCost n d N 1 m *
      (paperAtlasWeighted 1 m tau (incrementsOriginalMapCoordinates A B U)
        (incrementsOriginalDifferentiation A B) S).toReal) htau htau1
    (mul_nonneg (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _) ENNReal.toReal_nonneg)
    (mul_nonneg (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _) ENNReal.toReal_nonneg)
    (parameterRound2_original_map_weighted_source_germ_jets A B S hSO UI hUI hUIO hSUI F hF 2 m (by omega) tau htau hFfinite)
    (parameterRound2_original_map_weighted_source_germ_jets A B S hSO UI hUI hUIO hSUI U hU 1 m (by omega) tau htau hUfinite)
  refine ⟨h.1,h.2.1, h.2.2.trans_eq ?_⟩
  ring

#print axioms parameterRound2_original_metricCrossTerm_from_map_germ_norms
end
end GlobalEmbedding.Continuation
