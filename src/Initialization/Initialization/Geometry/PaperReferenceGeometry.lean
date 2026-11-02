import Initialization.Geometry.PaperNormBridge
import Initialization.Geometry.RescaledTransitionJets

/-!
# Original partial/MAX reference norms of the actual atlas and scaled metric

The same native chart transitions and the same native T²g coefficient operator
are expressed in genuine Pi coordinates. All constants precede the real scale,
and the maximum over chart pairs never contributes a growing cardinality.
-/

noncomputable section
open Set Function Metric Manifold IsManifold Bundle
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable (G : PreparedCharts M n)

/-- The genuine transition component norm on the entire actual overlap,
maximized over the actual scale-T atlas. -/
def initializationTransitionPaperCjNorm (j : ℕ) (T : ℝ) (hT : 1 ≤ T) : ENNReal :=
  paperAtlasCj j
    (fun ik : Fin (initializationAtlas G T hT).count × Fin (initializationAtlas G T hT).count ↦
      paperPiCoordinates (((initializationAtlas G T hT).chart ik.2) ∘
        ((initializationAtlas G T hT).chart ik.1).symm))
    (fun ik ↦ paperSourceDomain ((((initializationAtlas G T hT).chart ik.1).symm.trans
      ((initializationAtlas G T hT).chart ik.2)).source))
    (fun ik ↦ paperSourceDomain ((((initializationAtlas G T hT).chart ik.1).symm.trans
      ((initializationAtlas G T hT).chart ik.2)).source))

/-- Reference transition bounds in the original scalar partial/MAX norm.
The actual overlap domains, including the Pi/L² source conversion, are retained. -/
theorem exists_initializationTransition_paper_reference_bounds [CompactSpace M] :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧ ∀ (T : ℝ) (hT : 1 ≤ T) (j : ℕ),
      initializationTransitionPaperCjNorm G j T hT ≤ ENNReal.ofReal (B j) := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_boundedAtlas_transition_bounds G
  let L := (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap
  let factor := paperLinearCoordinateFactor (n := n) L
  have hf (j : ℕ) : 0 < factor j := paperLinearCoordinateFactor_pos L j
  have hs (j : ℕ) : 0 ≤ ∑ k ∈ Finset.range (j+1), B k :=
    Finset.sum_nonneg (fun k _ ↦ (hB k).le)
  refine ⟨fun j ↦ factor j * (1 + ∑ k ∈ Finset.range (j+1), B k),
    fun j ↦ mul_pos (hf j) (by linarith [hs j]), ?_⟩
  intro T hT j
  let Q := preparedCutoffsAt G T hT
  let atlas := Q.boundedAtlas hT
  let u := fun ik : Fin Q.count × Fin Q.count ↦
    atlas.chart ik.2 ∘ (atlas.chart ik.1).symm
  let U := fun ik : Fin Q.count × Fin Q.count ↦
    ((atlas.chart ik.1).symm.trans (atlas.chart ik.2)).source
  have hU (ik) : IsOpen (U ik) :=
    ((atlas.chart ik.1).symm.trans (atlas.chart ik.2)).open_source
  have hu (ik) : ContDiffOn ℝ ∞ (u ik) (U ik) := by
    have hleft := contMDiffOn_of_mem_maximalAtlas ((Q.boundedAtlas_smooth hT).chart_mem ik.2)
    have hright := contMDiffOn_symm_of_mem_maximalAtlas ((Q.boundedAtlas_smooth hT).chart_mem ik.1)
    exact (hleft.comp (hright.mono (fun _ hy ↦ hy.1)) (fun _ hy ↦ hy.2)).contDiffOn
  have hjets (ik) (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U ik) :
      ‖iteratedFDeriv ℝ k (u ik) y‖ ≤ B k :=
    hbound T hT Q ik.1 ik.2 k y hy
  have hbdd (ik) (k : ℕ) : BddAbove (Set.range fun x : U ik ↦
      ‖iteratedFDeriv ℝ k (u ik) x‖) :=
    ⟨B k, by rintro r ⟨x, rfl⟩; exact hjets ik k x x.property⟩
  have hp := paperAtlasCj_linearCoordinates_le j L u U hU hu (fun ik k _ ↦ hbdd ik k)
  have hn := finiteAtlasCjNorm_le_sum_of_jet_bounds j u U B (fun k ↦ (hB k).le)
    (fun ik k _ y hy ↦ hjets ik k y hy)
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (hn.trans (by linarith)) (hf j).le

variable
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- The actual coordinate matrix of T²g in the original paper norm. -/
def initializationTargetMetricPaperCjNorm (j : ℕ) (T : ℝ) (hT : 1 ≤ T) : ENNReal :=
  paperAtlasCj j
    (fun p : Fin (initializationAtlas G T hT).count ↦
      paperLinearCoordinates (metricPaperComponents n)
        (scaledTargetMetricOperator G g f (preparedCutoffsAt G T hT) p))
    (fun p ↦ paperSourceDomain (((initializationAtlas G T hT).chart p).target))
    (fun p ↦ paperSourceDomain (((initializationAtlas G T hT).chart p).target))

/-- The actual native scaled metric has all original partial/MAX reference
bounds, internally fixed before T. No metric or derivative budget is assumed. -/
theorem exists_initializationTargetMetric_paper_reference_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧ ∀ (T : ℝ) (hT : 1 ≤ T) (j : ℕ),
      initializationTargetMetricPaperCjNorm G g f j T hT ≤ ENNReal.ofReal (B j) := by
  obtain ⟨B, hB, hbound⟩ := exists_scaledTargetMetric_derivative_bounds G g f
  let L := metricPaperComponents n
  let factor := paperLinearCoordinateFactor (n := n) L
  have hf (j : ℕ) : 0 < factor j := paperLinearCoordinateFactor_pos L j
  have hs (j : ℕ) : 0 ≤ ∑ k ∈ Finset.range (j+1), B k :=
    Finset.sum_nonneg (fun k _ ↦ zero_le_one.trans (hB k))
  refine ⟨fun j ↦ factor j * (1 + ∑ k ∈ Finset.range (j+1), B k),
    fun j ↦ mul_pos (hf j) (by linarith [hs j]), ?_⟩
  intro T hT j
  let Q := preparedCutoffsAt G T hT
  let u := fun p : Fin Q.count ↦ scaledTargetMetricOperator G g f Q p
  let U := fun p : Fin Q.count ↦ ((Q.boundedAtlas hT).chart p).target
  have hU (p) : IsOpen (U p) := ((Q.boundedAtlas hT).chart p).open_target
  have hu (p) : ContDiffOn ℝ ∞ (u p) (U p) :=
    (scaledTargetMetricOperator_contDiffOn_wide G g f Q hT p).mono
      (ball_subset_closedBall.trans (Q.closedBall_subset_scaledTarget G hT p))
  have hjets (p) (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U p) :
      ‖iteratedFDeriv ℝ k (u p) y‖ ≤ B k := (hbound T hT Q p k y hy).2
  have hbdd (p) (k : ℕ) : BddAbove (Set.range fun x : U p ↦
      ‖iteratedFDeriv ℝ k (u p) x‖) :=
    ⟨B k, by rintro r ⟨x, rfl⟩; exact hjets p k x x.property⟩
  have hp := paperAtlasCj_linearCoordinates_le j L u U hU hu (fun p k _ ↦ hbdd p k)
  have hn := finiteAtlasCjNorm_le_sum_of_jet_bounds j u U B
    (fun k ↦ zero_le_one.trans (hB k)) (fun p k _ y hy ↦ hjets p k y hy)
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (hn.trans (by linarith)) (hf j).le

end GlobalEmbedding.Initialization
