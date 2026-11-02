import Repair.EntranceReferenceMetric
import Repair.EntranceFinitePlanAttachment
import Smoothing.ParameterRound2OriginalFixedPacket

/-!
# The actual original map and tensor terms of Given

The original map term has base weight two. The tensor term is the actual
induced metric of that same map. Both are produced from the original
full joint C(j+2) map bound, on exactly the original evaluation domains.
Only the remaining original fixed packet is supplied separately.

The finite-prefix theorem reads the map only through J+2. In particular
the actual entrance depth 197177 requires map bounds through 197179;
there is no uniform hypothesis on higher derivatives of the reference.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def repairEntranceOriginalGivenCost (n d N : ℕ)
    (map fixedPacket : ℕ → ℝ) (j : ℕ) : ℝ :=
  max ((j+1)*map (j+2))
    (max ((j+1)*(repairEntranceMetricCost n d N j*(map (j+2))^2)) (fixedPacket j))

theorem repairEntranceOriginalGivenCost_congr_prefix (n d N J : ℕ)
    (map map' fixedPacket fixedPacket' : ℕ → ℝ)
    (hmap : ∀ j, j ≤ J+2 → map j = map' j)
    (hfixed : ∀ j, j ≤ J → fixedPacket j = fixedPacket' j)
    (j : ℕ) (hj : j ≤ J) :
    repairEntranceOriginalGivenCost n d N map fixedPacket j =
      repairEntranceOriginalGivenCost n d N map' fixedPacket' j := by
  unfold repairEntranceOriginalGivenCost
  rw [hmap (j+2) (by omega),hfixed j hj]

def repairEntranceOriginalMapDepth : ℕ := repairEntrancePrimitiveDepth+2

theorem repairEntranceOriginalMapDepth_exact : repairEntranceOriginalMapDepth = 197179 := by
  norm_num [repairEntranceOriginalMapDepth,repairEntrancePrimitiveDepth]

private theorem entrance_original_weighted_top_bound
    {ι : Type*} [Fintype ι] {a q : ℕ} (base j : ℕ)
    (ell : ℝ) (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (C : ℝ) (hfinite : paperAtlasCj (j+base) f O S ≠ ⊤)
    (hbound : (paperAtlasCj (j+base) f O S).toReal ≤ C) :
    paperAtlasWeighted base j ell f O S ≠ ⊤ ∧
      (paperAtlasWeighted base j ell f O S).toReal ≤ (j+1)*C := by
  refine ⟨parameterRound2_paperAtlasWeighted_finite_of_topOrder base j ell f O S hfinite,?_⟩
  have h := parameterRound2_paperAtlasWeighted_le_topOrder base j hell0 hell1 f O S
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinite) h
  rw [ENNReal.toReal_mul] at hr
  have hcast : ((j : ℝ≥0∞)+1).toReal=(j : ℝ)+1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [hcast] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left hbound (by positivity))

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
private local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- Actual map and metric weighted inputs; norm finiteness is proved from
smoothness and compact samples, rather than added as a numerical input. -/
theorem repairEntrance_original_map_metric_weighted
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (j : ℕ) (ell R : ℝ) (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1) (hR : 0 ≤ R)
    (hbound : (paperAtlasCj (j+2) (incrementsOriginalMapCoordinates A B F)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ R) :
    let f := incrementsOriginalMapCoordinates A B F
    let g := incrementsOriginalTensorCoordinates A B
      (fun p x => inducedMetric (I := 𝓘(ℝ,Es)) (fun y => F (p,y)) x)
    let O := incrementsOriginalDifferentiation A B
    (paperAtlasWeighted 2 j ell f O S ≠ ⊤ ∧
      (paperAtlasWeighted 2 j ell f O S).toReal ≤ (j+1)*R) ∧
    (paperAtlasWeighted 0 j ell g O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell g O S).toReal ≤
        (j+1)*(repairEntranceMetricCost n d N j*R^2)) := by
  intro f g O
  have hf := parameterRound2_originalMapCoordinates_contDiffOn A B hA hB F hF
  have hfinite := parameterRound2_paperAtlasCj_finite_of_compact f O S
    (parameterRound2_originalDifferentiation_open A B) hS hSO hf (j+2)
  have hg := repairEntrance_inducedMetric_Cj_le A B hA hB S hSO F hF j R hR hfinite hbound
  refine ⟨entrance_original_weighted_top_bound 2 j ell hell0 hell1 f O S R hfinite hbound,?_⟩
  simpa only [Nat.add_zero] using entrance_original_weighted_top_bound 0 j ell hell0 hell1
    g O S (repairEntranceMetricCost n d N j*R^2) (by simpa using hg.1) (by simpa using hg.2)

/-- The reference H is the genuine induced metric. The map and tensor
parts of original Given are manufactured here, not assumed as outputs. -/
theorem repairEntrance_original_given_from_map_and_fixed
    (Data : IncrementsOriginalNativeData n d N M P)
    (hA : IsSmoothBufferedAtlas Data.atlas)
    (hB : ∀ i, Data.parameterChart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ Data.F)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (hH : Data.H = fun p x => inducedMetric (I := 𝓘(ℝ,Es)) (fun y => Data.F (p,y)) x)
    (j : ℕ) (ell R fixed : ℝ) (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1) (hR : 0 ≤ R)
    (hbound : (paperAtlasCj (j+2) (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ R)
    (hfixed : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hfixedBound : (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ fixed) :
    actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤
        max ((j+1)*R) (max ((j+1)*(repairEntranceMetricCost n d N j*R^2)) fixed) := by
  have h := repairEntrance_original_map_metric_weighted Data.atlas Data.parameterChart hA hB
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet) hS (fun _ _ hy => hy.1) Data.F hF
    j ell R hell0 hell1 hR hbound
  apply parameterRound2_originalGivenProfile_of_actual_map_tensor Data j ell hell1 _ _ _
    h.1.1 h.1.2 _ _ hfixed hfixedBound
  · rw [hH]; exact h.2.1
  · rw [hH]; exact h.2.2

/-- A finite original map class produces the original Given prefix at
every smoothing scale in [0,1]. All higher reference derivatives remain
unrestricted. -/
theorem repairEntrance_original_given_finite_class
    (Data : IncrementsOriginalNativeData n d N M P)
    (hA : IsSmoothBufferedAtlas Data.atlas)
    (hB : ∀ i, Data.parameterChart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ Data.F)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (hH : Data.H = fun p x => inducedMetric (I := 𝓘(ℝ,Es)) (fun y => Data.F (p,y)) x)
    (J : ℕ) (allowedMap fixedPacket : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J+2 → 0 ≤ allowedMap j)
    (hMap : ∀ j, j ≤ J+2 →
      (paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet)).toReal ≤ allowedMap j)
    (hFixed : ∀ j, j ≤ J → parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤ ∧
      (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ fixedPacket j) :
    ∀ j, j ≤ J → ∀ ell : ℝ, 0 ≤ ell → ell ≤ 1 →
      actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤
        repairEntranceOriginalGivenCost n d N allowedMap fixedPacket j := by
  intro j hj ell hell0 hell1
  exact repairEntrance_original_given_from_map_and_fixed Data hA hB hF hS hH j ell
    (allowedMap (j+2)) (fixedPacket j) hell0 hell1 (hAllowed (j+2) (by omega))
    (hMap (j+2) (by omega)) (hFixed j hj).1 (hFixed j hj).2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_original_map_metric_weighted
#print axioms GlobalEmbedding.Continuation.repairEntrance_original_given_finite_class
#print axioms GlobalEmbedding.Continuation.repairEntranceOriginalGivenCost_congr_prefix
#print axioms GlobalEmbedding.Continuation.repairEntranceOriginalMapDepth_exact
