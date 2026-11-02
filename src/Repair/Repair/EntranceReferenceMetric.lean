import Smoothing.ParameterRound2CrossInputJets
import Smoothing.ParameterRound2RepairRegularity
import Smoothing.ParameterRound2InitialCompact440

/-!
# The reference metric budget is produced by the reference map

The actual induced metric is one half of the actual self cross tensor.
The existing full joint cross estimate therefore supplies a numerical
Cj bound from the original C(j+2) map bound.  The constant depends on
dimensions and the observation order, and never on atlas count.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation

def repairEntranceMetricCost (n d N j : ℕ) : ℝ :=
  ((j+1)*linearModelFactor (parameterTensorModelEquiv n d).symm j*2^(j+1)*
    parameterRound2_mapWeightedJetCost n d N 2 j*
    parameterRound2_mapWeightedJetCost n d N 1 j)*(j+1)^2

theorem repairEntranceMetricCost_nonneg (n d N j : ℕ) :
    0 ≤ repairEntranceMetricCost n d N j := by
  unfold repairEntranceMetricCost
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (linearModelFactor_nonneg _ _)) (by positivity))
      (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _))
      (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _))
    (sq_nonneg _)

private theorem entrance_top_le_weighted_one
    {ι : Type*} [Fintype ι] {a q : ℕ} (j : ℕ)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ)) :
    paperAtlasCj j f O S ≤ paperAtlasWeighted 0 j 1 f O S := by
  unfold paperAtlasWeighted
  have h := Finset.single_le_sum
    (f := fun k : ℕ => ENNReal.ofReal (1 : ℝ)^k*paperAtlasCj (k+0) f O S)
    (fun _ _ => by positivity) (by simp : j ∈ Finset.range (j+1))
  simpa only [ENNReal.ofReal_one,one_pow,one_mul,Nat.add_zero] using h

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
private local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

/-- The true original reference metric has a finite class bound produced
from the map alone.  No independent metric-output estimate is assumed. -/
theorem repairEntrance_inducedMetric_Cj_le
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hfinite : paperAtlasCj (j+2) (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (hbound : (paperAtlasCj (j+2) (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ C) :
    let g := incrementsOriginalTensorCoordinates A B
      (fun p x => inducedMetric (I := IT) (fun y => F (p,y)) x)
    paperAtlasCj j g (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasCj j g (incrementsOriginalDifferentiation A B) S).toReal ≤
        repairEntranceMetricCost n d N j * C ^ 2 := by
  intro g
  let f := incrementsOriginalMapCoordinates A B F
  let O := incrementsOriginalDifferentiation A B
  let cross := incrementsOriginalTensorCoordinates A B
    (fun p x => metricCrossTerm (I := IT) (fun y => F (p,y)) (fun y => F (p,y)) x)
  have hW2 := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 j 1 f O S hfinite
  have hFinite1 : paperAtlasCj (j+1) f O S ≠ ⊤ := ne_top_of_le_ne_top hfinite
    (parameterRound2_paperAtlasCj_mono_order (by omega) f O S)
  have hW1 := parameterRound2_paperAtlasWeighted_finite_of_topOrder 1 j 1 f O S hFinite1
  have hcross := parameterRound2_original_metricCrossTerm_from_map_norms A B hA hB S hSO F F hF hF
    j 1 (by norm_num) le_rfl hW2 hW1
  dsimp only at hcross
  have hCrossTop := entrance_top_le_weighted_one j cross O S
  have hCrossFinite : paperAtlasCj j cross O S ≠ ⊤ := ne_top_of_le_ne_top hcross.1 hCrossTop
  have hcrossSmooth : ∀ i, ContDiffOn ℝ ∞ (cross i) (O i) :=
    parameterRound2_cross_originalCoordinates_contDiffOn A B hA hB F F hF hF
  have heq : g = fun i y => (1/2 : ℝ) • cross i y := by
    funext i y k
    dsimp only [g,cross,incrementsOriginalTensorCoordinates,metricCrossTerm,inducedMetric,
      LinearMap.add_apply,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hMetricLe : paperAtlasCj j g O S ≤ paperAtlasCj j cross O S := by
    rw [heq]
    apply (parameterRound2_paperAtlasCj_smul_le j cross O S
      (parameterRound2_originalDifferentiation_open A B) hSO hcrossSmooth hCrossFinite (1/2)).trans
    have hh : ENNReal.ofReal |(1/2 : ℝ)| ≤ 1 := by norm_num
    simpa only [one_mul] using mul_le_mul_left hh (paperAtlasCj j cross O S)
  refine ⟨ne_top_of_le_ne_top hCrossFinite hMetricLe,?_⟩
  have hw (base : ℕ) (hb : base ≤ 2)
      (hW : paperAtlasWeighted base j 1 f O S ≠ ⊤) :
      (paperAtlasWeighted base j 1 f O S).toReal ≤ (j+1)*C := by
    have htop : paperAtlasCj (j+base) f O S ≤ paperAtlasCj (j+2) f O S :=
      parameterRound2_paperAtlasCj_mono_order (by omega) f O S
    have hTopFinite := ne_top_of_le_ne_top hfinite htop
    have hWeighted := parameterRound2_paperAtlasWeighted_le_topOrder base j
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl f O S
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hTopFinite) hWeighted
    rw [ENNReal.toReal_mul] at hreal
    have hcast : ((j : ℝ≥0∞)+1).toReal=(j : ℝ)+1 := by
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simp
    rw [hcast] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_left
      ((ENNReal.toReal_mono hfinite htop).trans hbound) (by positivity))
  have hw2 := hw 2 le_rfl hW2
  have hw1 := hw 1 (by omega) hW1
  let K := (j+1)*linearModelFactor (parameterTensorModelEquiv n d).symm j*2^(j+1)*
    parameterRound2_mapWeightedJetCost n d N 2 j*parameterRound2_mapWeightedJetCost n d N 1 j
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (linearModelFactor_nonneg _ _)) (by positivity))
      (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _))
      (parameterRound2_mapWeightedJetCost_nonneg _ _ _ _ _)
  calc
    _ ≤ (paperAtlasWeighted 0 j 1 cross O S).toReal :=
      ENNReal.toReal_mono hcross.1 (hMetricLe.trans hCrossTop)
    _ ≤ K*(paperAtlasWeighted 2 j 1 f O S).toReal*
        (paperAtlasWeighted 1 j 1 f O S).toReal := hcross.2
    _ ≤ K*((j+1)*C)*((j+1)*C) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hw2 hK
      · exact hw1
      · exact ENNReal.toReal_nonneg
      · positivity
    _ = repairEntranceMetricCost n d N j * C ^ 2 := by
      dsimp only [K,repairEntranceMetricCost]
      ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_inducedMetric_Cj_le
#print axioms GlobalEmbedding.Continuation.repairEntranceMetricCost_nonneg
