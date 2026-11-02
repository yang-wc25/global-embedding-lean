import RepairClosure.InterfaceCanonicalApplicationMetric
import RepairClosure.InterfaceCanonicalApplicationLinearNorm
import OriginalAuxiliary.CanonicalReferenceBounds

/-!
# The actual initialization error in the original full tensor norm

The coordinate field estimated by initialization is identified, component
by component on the actual open charts, with the same native tensor
T²g - gamma(H). Its original full mixed-partial/MAX norm is then bounded
by a constant fixed before K,T and both chart counts, times K⁻¹ + K/T.

Boundedness of each real derivative supremum comes from the compact closed
ball inside the actual wider smooth chart. No finiteness is inferred from
a real-valued supremum without this boundedness proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set Function Metric
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalAuxiliary

def canonicalMetricErrorNormFactor (n d j : ℕ) : ℝ :=
  originalJointLinearNormFactor n d (-metricPaperComponents n) j

theorem canonicalMetricErrorNormFactor_pos (n d j : ℕ) :
    0 < canonicalMetricErrorNormFactor n d j :=
  originalJointLinearNormFactor_pos n d (-metricPaperComponents n) j

variable {n d N pc : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "I" => 𝓘(ℝ,Es)

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _))
  (frame : FullTangentFrame 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) (M := M) n)

include g frame


/-- Exact coefficient identity for the original target T²g. -/
theorem canonical_scaled_metric_coordinates_eqOn
    (T : ℝ) (hT : 1 ≤ T) (chart : Fin pc → OpenPartialHomeomorph P Ep)
    (i : Fin (initializationAtlas G T hT).count × Fin pc) :
    EqOn
      (incrementsOriginalTensorCoordinates (initializationAtlas G T hT) chart
        (fun _ x => canonicalScaledMetric g T x) i)
      (metricPaperComponents n ∘
        (scaledTargetMetricOperator G g frame (preparedCutoffsAt G T hT) i.1 ∘
          originalJointSourceProjection n d))
      (incrementsOriginalDifferentiation (initializationAtlas G T hT) chart i) := by
  intro z hz
  funext k
  let r := finProdFinEquiv.symm k
  have hk : finProdFinEquiv r = k := finProdFinEquiv.apply_symm_apply k
  have h := scaledTargetMetricOperator_inner G g frame (preparedCutoffsAt G T hT) hT
    i.1 hz.1 (EuclideanSpace.single r.1 1) (EuclideanSpace.single r.2 1)
  rw [← metricPaperComponents_apply] at h
  rw [hk] at h
  exact h.symm


/-- Smoothness of the same native scaled target on the original full
source/parameter differentiation domains. -/
theorem canonical_scaled_metric_coordinates_smooth
    (T : ℝ) (hT : 1 ≤ T) (chart : Fin pc → OpenPartialHomeomorph P Ep)
    (i : Fin (initializationAtlas G T hT).count × Fin pc) :
    ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates (initializationAtlas G T hT) chart
        (fun _ x => canonicalScaledMetric g T x) i)
      (incrementsOriginalDifferentiation (initializationAtlas G T hT) chart i) := by
  let Qscale := preparedCutoffsAt G T hT
  let A := initializationAtlas G T hT
  let pr := originalJointSourceProjection n d
  have hsub : (A.chart i.1).target ⊆ ((Qscale.scaledAtlas hT).chart i.1).target :=
    ball_subset_closedBall.trans (Qscale.closedBall_subset_scaledTarget G hT i.1)
  have hu := (scaledTargetMetricOperator_contDiffOn_wide G g frame Qscale hT i.1).mono hsub
  have hcomp : ContDiffOn ℝ ∞
      (metricPaperComponents n ∘ (scaledTargetMetricOperator G g frame Qscale i.1 ∘ pr))
      (incrementsOriginalDifferentiation A chart i) :=
    (metricPaperComponents n).contDiff.comp_contDiffOn
      (hu.comp pr.contDiff.contDiffOn (fun _ hz => hz.1))
  exact hcomp.congr (canonical_scaled_metric_coordinates_eqOn G g frame T hT chart i)

/-- The native tensor error has exactly the negative of the operator
defect already estimated in initialization, on the unchanged charts. -/
theorem canonical_scaled_metric_error_coordinates_eqOn
    (selector : FreeHopfProduct (fun _ : Fin n => G.palette) → EuclideanSpace ℝ (Fin N))
    (hSelector : ContMDiff (freeHopfModel (fun _ : Fin n => G.palette))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ selector)
    (K T : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (chart : Fin pc → OpenPartialHomeomorph P Ep)
    (i : Fin (initializationAtlas G T hT).count × Fin pc) :
    EqOn
      (incrementsOriginalTensorCoordinates (initializationAtlas G T hT) chart
        (fun _ x => canonicalScaledMetric g T x - inducedMetric («I» := I)
          (metricInitializationMap G g frame selector K T hK) x) i)
      ((-metricPaperComponents n) ∘
        (initializationMetricDefect G g frame selector K T hK hT i.1 ∘
          originalJointSourceProjection n d))
      (incrementsOriginalDifferentiation (initializationAtlas G T hT) chart i) := by
  intro z hz
  funext k
  let r := finProdFinEquiv.symm k
  have hk : finProdFinEquiv r = k := finProdFinEquiv.apply_symm_apply k
  have h := metricInitializationMap_native_metric_error G g frame selector hSelector hK
    (preparedCutoffsAt G T hT) hT i.1 hz.1
    (EuclideanSpace.single r.1 1) (EuclideanSpace.single r.2 1)
  change inner ℝ (initializationMetricDefect G g frame selector K T hK hT i.1
    (originalJointSourceProjection n d z) (EuclideanSpace.single r.1 1))
      (EuclideanSpace.single r.2 1) = _ at h
  rw [← metricPaperComponents_apply] at h
  rw [hk] at h
  change T^2 * g.inner _ _ _ - inducedMetric («I» := I)
    (metricInitializationMap G g frame selector K T hK) _ _ _ =
      -(metricPaperComponents n
        (initializationMetricDefect G g frame selector K T hK hT i.1
          (originalJointSourceProjection n d z)) k)
  rw [h]
  exact (neg_sub _ _).symm

/-- The original all-component, all-parameter Cj entrance error is a
proved output of the same initialization core. -/
theorem core_original_joint_metric_error_bounds
    (selector : FreeHopfProduct (fun _ : Fin n => G.palette) →
      EuclideanSpace ℝ (Fin (closedAmbientDimension n)))
    (B : InitializationReserves) (core : ColoredApproximationCore G g frame selector B)
    (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
    (chart : Fin pc → OpenPartialHomeomorph P Ep)
    (Omega : Fin (initializationAtlas G T (hK.trans hKT)).count → Set Es)
    (Q : Fin pc → Set Ep) (Kset : Set P) (j : ℕ) :
    paperAtlasCj j
      (incrementsOriginalTensorCoordinates (initializationAtlas G T (hK.trans hKT)) chart
        (fun _ x => canonicalScaledMetric g T x - inducedMetric («I» := I)
          (metricInitializationMap G g frame selector K T hK) x))
      (incrementsOriginalDifferentiation (initializationAtlas G T (hK.trans hKT)) chart)
      (incrementsOriginalEvaluation (initializationAtlas G T (hK.trans hKT))
        chart Omega Q Kset) ≤
      ENNReal.ofReal (canonicalMetricErrorNormFactor n d j * B.error j * (K⁻¹ + K/T)) := by
  let hT := hK.trans hKT
  let A := initializationAtlas G T hT
  let Qscale := preparedCutoffsAt G T hT
  let H := metricInitializationMap G g frame selector K T hK
  let defect := initializationMetricDefect G g frame selector K T hK hT
  have hH := core.map_smooth K T hK
  have hD (i : Fin A.count) :
      ContDiffOn ℝ ∞ (defect i) ((Qscale.scaledAtlas hT).chart i).target :=
    actualMetricDefect_contDiffOn_wide G g frame Qscale hT i H hH
  have hsub (i : Fin A.count) : (A.chart i).target ⊆
      ((Qscale.scaledAtlas hT).chart i).target :=
    ball_subset_closedBall.trans (Qscale.closedBall_subset_scaledTarget G hT i)
  have hR : 0 ≤ B.error j * (K⁻¹ + K/T) :=
    mul_nonneg (B.error_pos j).le ((initialization_error_scale_bounds hK hKT).2.2.1)
  have hBound := constant_parameter_original_linear_norm A chart Omega Q Kset defect
    (-metricPaperComponents n) (fun i => (hD i).mono (hsub i))
    j (B.error j * (K⁻¹ + K/T)) hR (by
      intro i k hk y hy
      have hBounded : ∀ a, a ≤ j → BddAbove (Set.range fun x : (A.chart i).target =>
          ‖iteratedFDeriv ℝ a (defect i) x‖) :=
        fun a _ => Qscale.boundedAtlas_jet_range_bddAbove G hT i _ (hD i) a
      have hChart := (finiteCjNorm_specification j (defect i)
        ((A.chart i).target) hBounded).2.1 k hk y hy
      have hAtlas := finiteCjNorm_le_finiteAtlasCjNorm j defect
        (fun p => (A.chart p).target) i
      exact (hChart.trans hAtlas).trans (core.metric_error K T hK hKT j))
  have hEq := paperAtlasCj_congr_on j
    (incrementsOriginalDifferentiation A chart)
    (incrementsOriginalEvaluation A chart Omega Q Kset) (fun _ _ hz => hz.1)
    (fun i => canonical_scaled_metric_error_coordinates_eqOn G g frame selector
      core.selector_smooth K T hK hT chart i)
  rw [hEq]
  convert hBound using 1 <;>
    simp only [canonicalMetricErrorNormFactor, mul_assoc]

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.canonical_scaled_metric_coordinates_smooth
#print axioms GlobalEmbedding.Continuation.RepairClosure.core_original_joint_metric_error_bounds
