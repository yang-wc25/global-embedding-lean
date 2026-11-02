import Repair.SourceCollarNovOriginalFactory
import Repair.ReferenceTemplateAdmissibility
import Repair.EntranceReferenceMetric
import Repair.IncrementOriginalGammaEllipticity

/-!
# Actual reference factories on the untouched original buffered atlas

The actual induced-metric C1 bound and its positive lower bound are derived
from the original map C3 bound and spatial ellipticity.  The original atlas,
parameter charts, sampling domains and factory budget are kept literally.
No convex source collar or independent induced-metric bound is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance novReferenceRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance novReferenceSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
private local instance novReferenceProductChart : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P D M
private local instance novReferenceProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

/-- All old seed-domain obligations follow from the original buffered
atlases and their original sampling inclusions. -/
theorem closureNov_original_seed_domains [CompactSpace P]
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Ep)
    (hTargetS : ∀ i, Omega i ⊆ (A.chart i).target)
    (hTargetP : ∀ i, Q i ⊆ (B.chart i).target)
    (hSamplingS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hSamplingP : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i)
    (hSource : 2 ≤ m+1) (hTarget : (m+1)*((m+1)+1)/2+1 ≤ N)
    (F0 : P × M → V) :
    RepairReferenceSeedDomains (sourceCollarNovOriginalSeed A B Omega Q F0) where
  source_dim := hSource
  target_dim := hTarget
  parameter_open := isOpen_univ
  parameter_compact := isCompact_univ
  parameter_subset := Subset.rfl
  atlas_smooth := hA
  parameter_charts_smooth := hB.chart_mem
  source_norm_subset := hTargetS
  source_inner_norm := by
    intro i x hx
    exact hSamplingS i (bufferedInner_subset_sampling A i (bufferedInnerCoordinates_mem A i hx))
  parameter_norm_subset := hTargetP
  parameter_cover := by
    intro p _
    obtain ⟨i,hi⟩ := B.cover p
    exact ⟨i,B.inner_subset i hi,
      hSamplingP i (bufferedInner_subset_sampling B i (bufferedInnerCoordinates_mem B i hi))⟩

/-- The original C3 map norm manufactures the old actual local factory.
All numerical hypotheses concern the one preassigned budget and original
input quantities.  In particular neither a normal, a collar, a decomposition
nor an induced-metric output estimate is supplied by the caller. -/
theorem closureNov_original_reference_local_factory
    (b : RepairReferenceFactoryBudget m d N)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Ep)
    (hSamplingS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hSamplingP : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i)
    (hRS : ∀ i x, x ∈ Omega i → ‖x‖ ≤ b.modelRadius)
    (hRP : ∀ i p, p ∈ Q i → ‖p‖ ≤ b.modelRadius)
    (hBS : b.buffer ≤ A.buffer) (hBP : b.buffer ≤ B.buffer)
    (hTensorBudget : repairEntranceMetricCost (m+1) d N 1*b.mapC3^2 ≤ b.tensorC1)
    (lower : ℝ) (hFirstLower : b.firstLower ≤ lower) (hTensorLower : b.tensorLower ≤ lower)
    (F0 : P × M → V) (hF : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ F0)
    (hMap3 : paperAtlasCj 3 (incrementsOriginalMapCoordinates A B.chart F0)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤ ENNReal.ofReal b.mapC3)
    (hEll : ∀ i z, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation A B.chart Omega Q univ i → ∀ v : D,
      lower*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => F0 ((B.chart i.2).symm z.1,x)) ∘
        (A.chart i.1).symm) z.2 v‖^2)
    (hPhase : ∀ i z, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation A B.chart Omega Q univ i →
      b.phaseMargin ≤ bestPhaseSupremum
        (repairReferenceFactoryField (sourceCollarNovOriginalSeed A B Omega Q F0)
          (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x) i z).1)
    (i : Fin A.count × Fin B.count) :
    Nonempty (RepairReferenceOriginalLocalFactory b
      (sourceCollarNovOriginalSeed A B Omega Q F0)
      (fun p => parameterRound2_native_source_slice_contMDiff hF p)
      (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) i
      (sourceCollarNovOriginalOuter A B i) (sourceCollarNovOriginalInner A B i) 0) := by
  let S := incrementsOriginalEvaluation A B.chart Omega Q univ
  have hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i := fun _ _ hy => hy.1
  have hMapFinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMap3
  have hMapReal : (paperAtlasCj 3 (incrementsOriginalMapCoordinates A B.chart F0)
      (incrementsOriginalDifferentiation A B.chart) S).toReal ≤ b.mapC3 := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hMap3).trans
      (by rw [ENNReal.toReal_ofReal b.mapC3_nonneg])
  have hMetric := repairEntrance_inducedMetric_Cj_le A B.chart hA hB.chart_mem S hSO
    F0 hF 1 b.mapC3 b.mapC3_nonneg hMapFinite hMapReal
  have hTensorBound : paperAtlasCj 1 (incrementsOriginalTensorCoordinates A B.chart
      (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x))
      (incrementsOriginalDifferentiation A B.chart) S ≤ ENNReal.ofReal b.tensorC1 := by
    calc
      _ = ENNReal.ofReal (paperAtlasCj 1 (incrementsOriginalTensorCoordinates A B.chart
        (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x))
        (incrementsOriginalDifferentiation A B.chart) S).toReal :=
          (ENNReal.ofReal_toReal hMetric.1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hMetric.2.trans hTensorBudget)
  have hInnerSample (z : X) (hz : z ∈ sourceCollarNovOriginalInner A B i) :
      parameterTensorModelEquiv (m+1) d z ∈ S i := by
    apply sourceCollarNov_original_samples A B Omega Q hSamplingS hSamplingP i z
    exact sourceCollarNov_original_buffer A B i b.buffer hBS hBP z hz
      (mem_ball_self b.buffer_pos)
  apply sourceCollarNov_original_local_factory b A hA B Omega Q hSamplingS hSamplingP
    hRS hRP hBS hBP F0 (fun p => parameterRound2_native_source_slice_contMDiff hF p)
    (parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB.chart_mem F0 hF)
    hMap3 (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x)
    (parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB.chart_mem F0 hF)
    hTensorBound (fun p x => (inducedMetric_isPosSemidef («I» := I) (fun y => F0 (p,y)) x).isSymm)
    i (fun z hz => hPhase i z (hInnerSample z hz))
  · intro z hz v
    have hSample := hInnerSample z hz
    have hx := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)=z.2 at hx
    have hzTarget : z.2 ∈ (A.chart i.1).target := by simpa only [hx] using hSample.1.1
    rw [increment_original_gamma_native_diag A B.chart hA F0
      (fun p => parameterRound2_native_source_slice_contMDiff hF p) i z hzTarget v]
    exact (mul_le_mul_of_nonneg_right hTensorLower (sq_nonneg ‖v‖)).trans (hEll i z hSample v)
  · intro z hz v
    exact (mul_le_mul_of_nonneg_right hFirstLower (sq_nonneg ‖v‖)).trans
      (hEll i z (sourceCollarNov_original_samples A B Omega Q hSamplingS hSamplingP i z hz) v)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.closureNov_original_seed_domains
#print axioms GlobalEmbedding.Continuation.closureNov_original_reference_local_factory
