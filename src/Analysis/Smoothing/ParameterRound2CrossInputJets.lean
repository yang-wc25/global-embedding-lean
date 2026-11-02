import Smoothing.ParameterRound2CrossNorms
import Probes.ActualCoreWeightedJets

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

def parameterRound2_mapWeightedJetCost (n d N base m : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap‖ *
    linearModelFactor (parameterTensorModelEquiv n d) (m+base) *
      coordinateDimensionFactor (n+d) (m+base)

theorem parameterRound2_mapWeightedJetCost_nonneg (n d N base m : ℕ) :
    0 ≤ parameterRound2_mapWeightedJetCost n d N base m :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (linearModelFactor_nonneg _ _))
    (coordinateDimensionFactor_nonneg _ _)

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2CrossInputChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CrossInputIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_nativeMapChart_eq_coordinate
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (F : P × M → Ey) (i : Fin A.count × Fin pcount) :
    (fun z : Ep × Es => F ((B i.2).symm z.1,(A.chart i.1).symm z.2)) =
      (EuclideanSpace.equiv (Fin N) ℝ).symm ∘ incrementsOriginalMapCoordinates A B F i ∘
        parameterTensorModelEquiv n d := by
  funext z
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) = z :=
    (parameterTensorModelEquiv n d).symm_apply_apply z
  have hp := congrArg Prod.fst hprod
  have hx := congrArg Prod.snd hprod
  dsimp only at hp hx
  simp only [Function.comp_apply,incrementsOriginalMapCoordinates,
    incrementsOriginalJointPoint,ContinuousLinearEquiv.symm_apply_apply]
  rw [hp,hx]

/-- Original map norm to actual source first-jet profile, retaining the full
parameter derivatives and every actual coordinate-change norm. -/
theorem parameterRound2_original_map_weighted_source_jets
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (base m : ℕ) (hbase : 1 ≤ base) (tau : ℝ) (htau : 0 < tau)
    (hfinite : paperAtlasWeighted base m tau (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤) :
    ∀ i : Fin A.count × Fin pcount, ∀ k ≤ m, ∀ z : Ep × Es,
      parameterTensorModelEquiv n d z ∈ S i →
      tau^k * ‖iteratedFDeriv ℝ k (fun w : Ep × Es =>
        fderiv ℝ (fun x => F ((B i.2).symm w.1,(A.chart i.1).symm x)) w.2) z‖ ≤
      parameterRound2_mapWeightedJetCost n d N base m *
        (paperAtlasWeighted base m tau (incrementsOriginalMapCoordinates A B F)
          (incrementsOriginalDifferentiation A B) S).toReal := by
  intro i k hk z hz
  let f := fun z : Ep × Es => F ((B i.2).symm z.1,(A.chart i.1).symm z.2)
  let O := (B i.2).target ×ˢ (A.chart i.1).target
  have hO : IsOpen O := (B i.2).open_target.prod (A.chart i.1).open_target
  have hf : ContDiffOn ℝ ∞ f O := parameterRound2_nativeMapChart_contDiffOn A B hA hB F hF i
  have hzO : z ∈ O := by
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z),
        incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) = z :=
      (parameterTensorModelEquiv n d).symm_apply_apply z
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have hd := spatial_first_jet_le hO hf hzO k
  have hj := paperAtlasWeighted_native_shifted_joint_jet_le (parameterTensorModelEquiv n d)
    (EuclideanSpace.equiv (Fin N) ℝ).symm base m tau htau
    (incrementsOriginalMapCoordinates A B F) (incrementsOriginalDifferentiation A B) S
    (parameterRound2_originalDifferentiation_open A B) hSO
    (parameterRound2_originalMapCoordinates_contDiffOn A B hA hB F hF)
    hfinite i hk hbase hz
  rw [← parameterRound2_nativeMapChart_eq_coordinate A B F i] at hj
  exact (mul_le_mul_of_nonneg_left hd (pow_nonneg htau.le k)).trans hj

/-- Actual map norms imply the actual original cross tensor norm. There is
no assumed metric or repair-error estimate. -/
theorem parameterRound2_original_metricCrossTerm_from_map_norms
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F U : P × M → Ey)
    (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (hU : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ U)
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
    paperAtlasWeighted 0 m tau C (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 m tau C (incrementsOriginalDifferentiation A B) S).toReal ≤
        ((m+1) * linearModelFactor (parameterTensorModelEquiv n d).symm m * 2^(m+1) *
          parameterRound2_mapWeightedJetCost n d N 2 m *
          parameterRound2_mapWeightedJetCost n d N 1 m) * WF * WU := by
  dsimp only
  have h := parameterRound2_original_metricCrossTerm_weighted_norm A B hA hB S hSO F U hF hU m tau
    (parameterRound2_mapWeightedJetCost n d N 2 m *
      (paperAtlasWeighted 2 m tau (incrementsOriginalMapCoordinates A B F)
        (incrementsOriginalDifferentiation A B) S).toReal)
    (parameterRound2_mapWeightedJetCost n d N 1 m *
      (paperAtlasWeighted 1 m tau (incrementsOriginalMapCoordinates A B U)
        (incrementsOriginalDifferentiation A B) S).toReal) htau htau1
    (mul_nonneg (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _) ENNReal.toReal_nonneg)
    (mul_nonneg (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _) ENNReal.toReal_nonneg)
    (parameterRound2_original_map_weighted_source_jets A B hA hB S hSO F hF 2 m (by omega) tau htau hFfinite)
    (parameterRound2_original_map_weighted_source_jets A B hA hB S hSO U hU 1 m (by omega) tau htau hUfinite)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

#print axioms parameterRound2_original_map_weighted_source_jets
#print axioms parameterRound2_original_metricCrossTerm_from_map_norms
end
end GlobalEmbedding.Continuation
