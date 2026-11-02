import RepairClosure.UniformRepairStatements
import OriginalAuxiliary.CanonicalReferenceBounds

/-!
# Actual initialization supplies the independent coordinate repair inputs

This file imports no completed repair theorem. Starting with the original
`InitializationData`, it manufactures the reference core and the numerical
coordinate margin in the independently stated repair contract. The same
reserve and phase constants precede both frequencies, the parameter space,
its dimension, and the receiving original geometry.

The auxiliary tangent norm is unchanged. Its actual native margin grows
as T², while the actual forward coordinate comparison is bounded by T² C;
the proved cancellation gives the fixed coordinate margin mu / C.
No reference estimates, phase margin, or comparison are supplied as inputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set Function
open scoped ContDiff Topology

universe uM uP
namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIntegration OriginalAuxiliary

private local instance canonicalContractProductChart {n d : ℕ} {M P : Type*}
    [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P] :
    ChartedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace _ _ _ _

private local instance canonicalContractProductManifold {n d : ℕ} {M P : Type*}
    [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] :
    IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ,EuclideanSpace ℝ (Fin n))) (n := ∞) P M

/-- The literal original component-partial reference profile of the
constant-parameter initialization map. -/
def canonicalRepairReferenceProfile (n d : ℕ) (B : InitializationReserves) (j : ℕ) : ℝ :=
  constantParameterNormFactor n d (closedAmbientDimension n) j * B.map j

theorem canonicalRepairReferenceProfile_nonneg
    (n d : ℕ) (B : InitializationReserves) (j : ℕ) :
    0 ≤ canonicalRepairReferenceProfile n d B j :=
  (mul_pos (constantParameterNormFactor_pos _ _ _ j) (B.map_pos j)).le

variable {m : ℕ} {M : Type uM} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin (closedAmbientDimension (m+1)))
local notation "I" => 𝓘(ℝ,Es)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- The independently defined reference assumptions are outputs of the
original initialization construction, uniformly before every frequency.
The order J is arbitrary, and even the parameter dimension follows the
fixed initialization reserves. -/
theorem InitializationData.exists_independent_coordinate_references
    [IsContinuousRiemannianBundle Es (TangentSpace I : M → Type _)]
    (data : InitializationData M m) (hm : 1 ≤ m)
    (metric0 : ContMDiffRiemannianMetric I ∞ Es (TangentSpace I : M → Type _)) :
    ∃ (B : InitializationReserves) (mu C : ℝ),
      ColoredApproximationCore data.charts metric0 data.frame data.phase.selector B ∧
      0 < mu ∧ 0 < C ∧
      (∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        B.K₀ ≤ K → B.R₀*K ≤ T → ∀ x : M,
        T^2*mu ≤ truePhaseMargin
          (metricInitializationMap data.charts metric0 data.frame data.phase.selector K T hK)
          (data.map_smooth metric0 K T hK) x) ∧
      (∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        B.K₀ ≤ K → B.R₀*K ≤ T →
        ∀ (d : ℕ) (b : OriginalRepairGeometryBudget)
          (P : Type uP) [TopologicalSpace P] [T2Space P] [CompactSpace P]
          [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
          [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
          (g : OriginalRepairGeometry b (m+1) d M P),
          g.atlas = initializationAtlas data.charts T (hK.trans hKT) → ∀ J : ℕ,
        let F0 : P × M → V := fun px =>
          metricInitializationMap data.charts metric0 data.frame data.phase.selector K T hK px.2
        RepairReferenceCore g (canonicalRepairReferenceProfile (m+1) d B)
          B.mapLower J F0 ∧ CoordinateReferencePhase g (mu/C) F0) := by
  obtain ⟨B,mu,C,hB,hmu,hC,hNative,hFactory⟩ :=
    InitializationData.exists_original_factory_scale_control data hm metric0
  refine ⟨B,mu,C,hB,hmu,hC,hNative,?_⟩
  intro K T hK hKT hK0 hR0 d b P topologyP hausdorffP compactP chartsP smoothP g hAtlas J
  dsimp only
  let F0 : P × M → V := fun px =>
    metricInitializationMap data.charts metric0 data.frame data.phase.selector K T hK px.2
  rcases g with ⟨A,Omega,pc,chart,Q,support,hSource,hParam,hA,hChart,
    hDegree,hPdegree,hRaw,hPraw,hPtrans,hStrans⟩
  change A = initializationAtlas data.charts T (hK.trans hKT) at hAtlas
  subst A
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · change ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d) × Es) 𝓘(ℝ,V) ∞ F0
    rw [modelWithCornersSelf_prod]
    exact (data.map_smooth metric0 K T hK).comp contMDiff_snd
  · intro j _
    exact core_original_joint_map_bounds data.charts metric0 data.frame data.phase.selector
      B hB K T hK hKT chart Omega Q univ j
  · intro p i y hy v
    exact core_original_map_ellipticity data.charts metric0 data.frame data.phase.selector
      B hB K T hK hKT hK0 hR0 i y (hSource.norm_target i hy) v
  · intro i z hz
    exact hFactory K T hK hKT hK0 hR0 d pc P chart Omega hSource.norm_target Q univ univ
      (fun p x => inducedMetric («I» := I) (fun y => F0 (p,y)) x) i z hz

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.canonicalRepairReferenceProfile_nonneg
#print axioms GlobalEmbedding.Continuation.RepairClosure.InitializationData.exists_independent_coordinate_references
