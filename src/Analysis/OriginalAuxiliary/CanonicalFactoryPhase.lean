import OriginalAuxiliary.CanonicalScaleMargin
import FaithfulCollars.OriginalFactoryReindex

/-!
# Actual original repair factory supplied by the canonical scale family

The fixed positive factory margin is manufactured from initialization data.
Its proof passes through the original auxiliary tangent norm: the very same
H has native margin at least T² mu, and the very same T-atlas has forward
comparison at most T² C. Their exact quotient supplies the original
`repairReferenceFactoryField`, on the caller's unchanged Omega/Q/K/U.

No native margin, auxiliary comparison, chart-count bound or replacement
map is an input. This theorem is an actual family producer; it does not
assert a comparison for arbitrary unrelated atlases or auxiliary metrics.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set Metric
open scoped ContDiff Topology

universe uP
namespace GlobalEmbedding.Continuation.OriginalAuxiliary
open FaithfulCollars

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "I" => 𝓘(ℝ, D)

attribute [-instance] instNormedAddCommGroupTangentSpaceReal_globalEmbedding
  instNormedSpaceRealTangentSpace_globalEmbedding in
/-- The complete phase producer on the literal original repair factory.
The two numerical constants precede K, T, every scale-atlas patch, the
finite parameter chart count and all original evaluation domains. -/
theorem InitializationData.exists_original_factory_scale_control
    [IsContinuousRiemannianBundle D (TangentSpace I : M → Type _)]
    (data : InitializationData M m) (hm : 1 ≤ m)
    (g : ContMDiffRiemannianMetric I ∞ D (TangentSpace I : M → Type _)) :
    ∃ (B : InitializationReserves) (mu C : ℝ),
      ColoredApproximationCore data.charts g data.frame data.phase.selector B ∧
      0 < mu ∧ 0 < C ∧
      (∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        B.K₀ ≤ K → B.R₀ * K ≤ T → ∀ x : M,
        T^2 * mu ≤ truePhaseMargin
          (metricInitializationMap data.charts g data.frame data.phase.selector K T hK)
          (data.map_smooth g K T hK) x) ∧
      (∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
        B.K₀ ≤ K → B.R₀ * K ≤ T →
        ∀ (d pc : ℕ) (P : Type uP) [TopologicalSpace P]
        (chart : Fin pc → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
        (Omega : Fin (initializationAtlas data.charts T (hK.trans hKT)).count → Set D),
        (∀ i, Omega i ⊆ ((initializationAtlas data.charts T (hK.trans hKT)).chart i).target) →
        ∀ (Q : Fin pc → Set (EuclideanSpace ℝ (Fin d))) (Kset U : Set P)
        (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
        (i : Fin (initializationAtlas data.charts T (hK.trans hKT)).count × Fin pc)
        (z : EuclideanSpace ℝ (Fin d) × D),
        parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation
          (initializationAtlas data.charts T (hK.trans hKT)) chart Omega Q Kset i →
        mu / C ≤ bestPhaseSupremum
          (repairReferenceFactoryField
            (originalReferenceSeed (initializationAtlas data.charts T (hK.trans hKT))
              Omega chart Q Kset U
              (fun px => metricInitializationMap data.charts g data.frame data.phase.selector
                K T hK px.2)) Htensor i z).1) := by
  obtain ⟨B,mu,C,hB,hmu,hC,hForward,hNative⟩ :=
    InitializationData.exists_original_scale_control data hm g
  refine ⟨B,mu,C,hB,hmu,hC,hNative,?_⟩
  intro K T hK hKT hK0 hR0 d pc P topologyP chart Omega hTarget Q Kset U Htensor i z hz
  let A := initializationAtlas data.charts T (hK.trans hKT)
  let H := metricInitializationMap data.charts g data.frame data.phase.selector K T hK
  have hH := data.map_smooth g K T hK
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at hx
  have hy : z.2 ∈ (A.chart i.1).target :=
    hTarget i.1 (by simpa only [hx] using hz.2.1)
  have hTp : 0 < T := zero_lt_one.trans_le (hK.trans hKT)
  have hScaleC : 0 < T^2 * C := mul_pos (sq_pos_of_pos hTp) hC
  have hBound := hForward T (hK.trans hKT) i.1 z.2 hy
  have hMargin := hNative K T hK hKT hK0 hR0 ((A.chart i.1).symm z.2)
  have hTransport := increment_original_true_phase_to_coordinate (by omega : 2 ≤ m+1)
    (fun (_ : ℝ) x => H x) (fun _ => hH)
    (fun _ => A.chart i.1) (fun _ => (hB.atlas_smooth T (hK.trans hKT)).chart_mem i.1)
    (Set.univ ×ˢ (A.chart i.1).target)
    (isOpen_univ.prod (A.chart i.1).open_target)
    (repair_reference_slice_joint_smooth H hH (A.chart i.1)
      ((hB.atlas_smooth T (hK.trans hKT)).chart_mem i.1))
    (0,z.2) ⟨mem_univ _,hy⟩ hy (T^2*C) hScaleC hBound
  have hResult := (div_le_div_of_nonneg_right hMargin hScaleC.le).trans hTransport
  rw [compensated_margin_ratio mu C T hC hTp] at hResult
  exact hResult

end GlobalEmbedding.Continuation.OriginalAuxiliary

#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.InitializationData.exists_original_factory_scale_control
