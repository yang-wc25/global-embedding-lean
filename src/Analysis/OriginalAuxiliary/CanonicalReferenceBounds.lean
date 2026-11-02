import OriginalAuxiliary.ConstantParameterNorm

/-!
# Actual initialization reference bounds in the original repair norm

The all-order Euclidean atlas bounds of the constructed map are converted
to the literal full source/parameter mixed-partial MAX norm. Genuine jet
boundedness is supplied on compact cores of the wider actual charts before
using the real finite atlas norm. Ellipticity uses the actual derivative
of the same map and the same charts.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalAuxiliary

variable {n d N pc : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "I" => 𝓘(ℝ,Es)

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (frame : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
  (selector : FreeHopfProduct (fun _ : Fin n => G.palette) →
    EuclideanSpace ℝ (Fin (closedAmbientDimension n)))
  (B : InitializationReserves) (core : ColoredApproximationCore G g frame selector B)

include g frame core


theorem core_original_joint_map_bounds
    (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
    (chart : Fin pc → OpenPartialHomeomorph P Ep)
    (Omega : Fin (initializationAtlas G T (hK.trans hKT)).count → Set Es)
    (Q : Fin pc → Set Ep) (Kset : Set P) (j : ℕ) :
    paperAtlasCj j
      (incrementsOriginalMapCoordinates (initializationAtlas G T (hK.trans hKT)) chart
        (fun px => metricInitializationMap G g frame selector K T hK px.2))
      (incrementsOriginalDifferentiation (initializationAtlas G T (hK.trans hKT)) chart)
      (incrementsOriginalEvaluation (initializationAtlas G T (hK.trans hKT))
        chart Omega Q Kset) ≤
      ENNReal.ofReal (constantParameterNormFactor n d (closedAmbientDimension n) j * B.map j) := by
  let hT := hK.trans hKT
  let A := initializationAtlas G T hT
  let Qscale := preparedCutoffsAt G T hT
  let H := metricInitializationMap G g frame selector K T hK
  have hH := core.map_smooth K T hK
  apply constant_parameter_original_map_norm A (core.atlas_smooth T hT) chart Omega Q Kset
    H hH j (B.map j) (B.map_pos j).le
  intro i k hk y hy
  have hWide := Qscale.boundedAtlas_pullback_contDiffOn_wide G hT i H hH
  have hBounded : ∀ a, a ≤ j → BddAbove (Set.range fun x : (A.chart i).target =>
      ‖iteratedFDeriv ℝ a (H ∘ (A.chart i).symm) x‖) := by
    intro a _
    exact Qscale.boundedAtlas_jet_range_bddAbove G hT i _ hWide a
  have hChart := (finiteCjNorm_specification j (H ∘ (A.chart i).symm)
    ((A.chart i).target) hBounded).2.1 k hk y hy
  have hAtlas := finiteCjNorm_le_finiteAtlasCjNorm j
    (fun p : Fin A.count => H ∘ (A.chart p).symm)
    (fun p => (A.chart p).target) i
  exact (hChart.trans hAtlas).trans (core.map_reference K T hK hKT j)

theorem core_original_map_ellipticity
    (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
    (hK0 : B.K₀ ≤ K) (hR0 : B.R₀*K ≤ T)
    (i : Fin (initializationAtlas G T (hK.trans hKT)).count) (y : Es)
    (hy : y ∈ ((initializationAtlas G T (hK.trans hKT)).chart i).target) (v : Es) :
    B.mapLower * ‖v‖^2 ≤ ‖fderiv ℝ
      (metricInitializationMap G g frame selector K T hK ∘
        ((initializationAtlas G T (hK.trans hKT)).chart i).symm) y v‖^2 := by
  have h := (core.map_ellipticity K T hK hKT hK0 hR0 i y hy v).1
  simpa only [actualMetricOperator_inner, real_inner_self_eq_norm_sq] using h

end GlobalEmbedding.Continuation.OriginalAuxiliary
#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.core_original_joint_map_bounds
#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.core_original_map_ellipticity

