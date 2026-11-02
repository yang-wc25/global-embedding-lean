import Repair.ClosureNovOriginalReference
import Repair.SourceCollarNovParentProduct

/-!
# Actual factories with parent collars inside the original inner domains

The auxiliary observation parents are fixed scalar functions of the original
raw preparation.  Their actual carriers and open neighborhoods are constructed
on the same A/B/Omega/Q.  This producer satisfies the older interaction
consumer's inner-domain requirement without assuming a convex collar.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance novParentFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance novParentFactorySquareNormed {E : Type*}
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
private local instance novParentFactoryProductChart : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P D M
private local instance novParentFactoryProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

omit [BoundarylessManifold 𝓘(ℝ,D) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,D) : M → Type _)] in
/-- A reusable original-map-to-induced-metric estimate.  Its only analytic
input is the original map C3 bound. -/
theorem closureNov_original_metric_bound
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Ep)
    (R3 : ℝ) (hR3 : 0 ≤ R3)
    (F0 : P × M → V) (hF : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ F0)
    (hMap : paperAtlasCj 3 (incrementsOriginalMapCoordinates A B.chart F0)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤ ENNReal.ofReal R3) :
    paperAtlasCj 1 (incrementsOriginalTensorCoordinates A B.chart
      (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x))
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤
      ENNReal.ofReal (repairEntranceMetricCost (m+1) d N 1*R3^2) := by
  have hFinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMap
  have hReal : (paperAtlasCj 3 (incrementsOriginalMapCoordinates A B.chart F0)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ R3 :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hMap).trans
      (by rw [ENNReal.toReal_ofReal hR3])
  have hMetric := repairEntrance_inducedMetric_Cj_le A B.chart hA hB.chart_mem
    (incrementsOriginalEvaluation A B.chart Omega Q univ) (fun _ _ hy => hy.1)
    F0 hF 1 R3 hR3 hFinite hReal
  rw [← ENNReal.ofReal_toReal hMetric.1]
  exact ENNReal.ofReal_le_ofReal hMetric.2

/-- The factory's entire open source domain pulls back to the original
inner domains.  Every geometric premise is produced from original buffers,
original raw preparation and its original first derivative bound. -/
theorem closureNov_original_parent_local_factory
    (b : RepairReferenceFactoryBudget m d N)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorRawCutoffPreparation B BP TP Dp)
    (hBS : 0 ≤ BS 1) (hBP : 0 ≤ BP 1)
    (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Ep)
    (hSamplingS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hSamplingP : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i)
    (hRS : ∀ i x, x ∈ Omega i → ‖x‖ ≤ b.modelRadius)
    (hRP : ∀ i p, p ∈ Q i → ‖p‖ ≤ b.modelRadius)
    (hBufferS : b.buffer ≤ sourceCollarNovParentRadius A BS)
    (hBufferP : b.buffer ≤ sourceCollarNovParentRadius B BP)
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
      (sourceCollarNovParentProductDomain RS RP i) (sourceCollarNovParentProductCarrier RS RP i) 0) := by
  let S := incrementsOriginalEvaluation A B.chart Omega Q univ
  have hSample (z : X) (hz : z ∈ sourceCollarNovParentProductDomain RS RP i) :
      parameterTensorModelEquiv (m+1) d z ∈ S i :=
    sourceCollarNov_original_samples A B Omega Q hSamplingS hSamplingP i z
      (sourceCollarNovParentProduct_domain_original RS RP i hz)
  have hInnerSample (z : X) (hz : z ∈ sourceCollarNovParentProductCarrier RS RP i) :
      parameterTensorModelEquiv (m+1) d z ∈ S i := by
    apply hSample
    exact sourceCollarNovParentProduct_buffer RS RP hA hB hBS hBP
      b.buffer hBufferS hBufferP i z hz (mem_ball_self b.buffer_pos)
  have hTensor := (closureNov_original_metric_bound A hA B hB Omega Q
    b.mapC3 b.mapC3_nonneg F0 hF hMap3).trans (ENNReal.ofReal_le_ofReal hTensorBudget)
  apply repair_reference_original_local_factory_buffered b
    (sourceCollarNovOriginalSeed A B Omega Q F0)
    (fun p => parameterRound2_native_source_slice_contMDiff hF p) S
    (fun _ _ hy => hy.1)
    (parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB.chart_mem F0 hF)
    hMap3 (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x)
    (parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB.chart_mem F0 hF)
    hTensor (fun p x => (inducedMetric_isPosSemidef («I» := I) (fun y => F0 (p,y)) x).isSymm)
    i (hA.chart_mem i.1) (sourceCollarNovParentProductDomain RS RP i)
    (sourceCollarNovParentProductCarrier RS RP i) 0
    (sourceCollarNovParentProduct_domain_open RS RP i) hSample
    ((sourceCollarNovParentProduct_carrier_original RS RP i).trans
      (sourceCollarNov_original_inner_bounded A B Omega Q hSamplingS hSamplingP
        b.modelRadius hRS hRP i))
    (sourceCollarNovParentProduct_buffer RS RP hA hB hBS hBP b.buffer hBufferS hBufferP i)
    (fun z hz => hPhase i z (hInnerSample z hz))
  · intro z hz v
    have hS := hInnerSample z hz
    have hx := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)=z.2 at hx
    have hzTarget : z.2 ∈ (A.chart i.1).target := by simpa only [hx] using hS.1.1
    change b.tensorLower*‖v‖^2 ≤ round4OriginalNativeTensorCoordinates A B.chart
      (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x) i z v v
    rw [increment_original_gamma_native_diag A B.chart hA F0
      (fun p => parameterRound2_native_source_slice_contMDiff hF p) i z hzTarget v]
    exact (mul_le_mul_of_nonneg_right hTensorLower (sq_nonneg ‖v‖)).trans (hEll i z hS v)
  · intro z hz v
    exact (mul_le_mul_of_nonneg_right hFirstLower (sq_nonneg ‖v‖)).trans (hEll i z (hSample z hz) v)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.closureNov_original_metric_bound
#print axioms GlobalEmbedding.Continuation.closureNov_original_parent_local_factory
