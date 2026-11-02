import Initialization.Assembly.FixedConstruction
import Initialization.Assembly.RescaledNorms
import Initialization.Colored.ActualNativeMetric
import Initialization.Colored.ActualMapEllipticity
import Initialization.Phase.ActualPhaseMargin
import Initialization.Phase.NativeChartPhase

/-!
# All actual geometric and analytic conclusions of colored initialization

The reserves in this file are outputs, selected before the real frequencies.
The map and atlas in every field are the same explicit constructions. This
file uses the stronger operator-valued Fréchet norm; the final entry also
exports the original component-partial paper norm through its proved bridge.
-/

noncomputable section
open Bundle Manifold Set Metric IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

/-- A fixed reserve consists only of constants and sequences, never of a
frequency-dependent choice or a supplied geometric estimate. -/
structure InitializationReserves where
  value : ℝ
  degree : ℕ
  transition : ℕ → ℝ
  metric : ℕ → ℝ
  map : ℕ → ℝ
  error : ℕ → ℝ
  lower : ℝ
  upper : ℝ
  mapLower : ℝ
  mapUpper : ℝ
  margin : ℝ
  K₀ : ℝ
  R₀ : ℝ
  value_nonneg : 0 ≤ value
  transition_pos : ∀ j, 0 < transition j
  metric_one_le : ∀ j, 1 ≤ metric j
  map_pos : ∀ j, 0 < map j
  error_pos : ∀ j, 0 < error j
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  mapLower_pos : 0 < mapLower
  mapUpper_pos : 0 < mapUpper
  margin_pos : 0 < margin
  K₀_one_le : 1 ≤ K₀
  R₀_one_le : 1 ≤ R₀

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

/-- A transparent conjunction of the actual initialization conclusions. All
fields refer to the constructed H and T-scale atlas; none is a hypothesis of
the existence theorem. -/
structure ColoredApproximationCore
    (G : PreparedCharts M n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
    (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) →
      EuclideanSpace ℝ (Fin (closedAmbientDimension n)))
    (B : InitializationReserves) : Prop where
  colors_two_le : 2 ≤ G.palette
  selector_smooth : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (closedAmbientDimension n))) ∞ S
  selector_gram : ∀ z, Matrix.gram ℝ
    (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ G.palette) l S z) = 1
  map_smooth : ∀ (K T : ℝ) (hK : 1 ≤ K),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (closedAmbientDimension n))) ∞
      (metricInitializationMap G g f S K T hK)
  map_value : ∀ (K T : ℝ) (hK : 1 ≤ K) (x : M),
    ‖metricInitializationMap G g f S K T hK x‖ ≤ B.value
  atlas_smooth : ∀ (T : ℝ) (hT : 1 ≤ T),
    IsSmoothBufferedAtlas (initializationAtlas G T hT)
  atlas_target : ∀ (T : ℝ) (hT : 1 ≤ T) (i : Fin (initializationAtlas G T hT).count),
    ((initializationAtlas G T hT).chart i).target = ball 0 G.scaleRadius
  atlas_buffer : ∀ (T : ℝ) (hT : 1 ≤ T),
    (initializationAtlas G T hT).buffer = G.scaleRadius / 2
  chart_formula : ∀ (T : ℝ) (hT : 1 ≤ T)
    (i : Fin (initializationAtlas G T hT).count) (x : M),
    (initializationAtlas G T hT).chart i x =
      T • (G.chart ((preparedCutoffsAt G T hT).parent i) x -
        (preparedCutoffsAt G T hT).center i)
  inverse_chart_formula : ∀ (T : ℝ) (hT : 1 ≤ T)
    (i : Fin (initializationAtlas G T hT).count) (y : EuclideanSpace ℝ (Fin n)),
    ((initializationAtlas G T hT).chart i).symm y =
      (G.chart ((preparedCutoffsAt G T hT).parent i)).symm
        (T⁻¹ • y + (preparedCutoffsAt G T hT).center i)
  inner_support : ∀ (T : ℝ) (hT : 1 ≤ T) (i : Fin (initializationAtlas G T hT).count),
    (initializationAtlas G T hT).inner i ⊆ (initializationAtlas G T hT).support i
  support_compact : ∀ (T : ℝ) (hT : 1 ≤ T) (i : Fin (initializationAtlas G T hT).count),
    IsCompact ((initializationAtlas G T hT).support i)
  support_degree : ∀ (T : ℝ) (hT : 1 ≤ T),
    (initializationAtlas G T hT).supportDegree ≤ B.degree
  transition_reference : ∀ (T : ℝ) (hT : 1 ≤ T)
    (i k : Fin (initializationAtlas G T hT).count) (j : ℕ) (y : EuclideanSpace ℝ (Fin n)),
    y ∈ (((initializationAtlas G T hT).chart i).symm.trans
      ((initializationAtlas G T hT).chart k)).source →
    ‖iteratedFDeriv ℝ j
      ((initializationAtlas G T hT).chart k ∘ ((initializationAtlas G T hT).chart i).symm) y‖ ≤
      B.transition j
  metric_reference : ∀ (T : ℝ) (hT : 1 ≤ T)
    (i : Fin (initializationAtlas G T hT).count) (j : ℕ) (y : EuclideanSpace ℝ (Fin n)),
    y ∈ ((initializationAtlas G T hT).chart i).target →
    ‖iteratedFDeriv ℝ j
      (scaledTargetMetricOperator G g f (preparedCutoffsAt G T hT) i) y‖ ≤ B.metric j
  metric_ellipticity : ∀ (T : ℝ) (hT : 1 ≤ T)
    (i : Fin (initializationAtlas G T hT).count) (y : EuclideanSpace ℝ (Fin n)),
    y ∈ ((initializationAtlas G T hT).chart i).target → ∀ v : EuclideanSpace ℝ (Fin n),
    B.lower * ‖v‖ ^ 2 ≤
      inner ℝ (scaledTargetMetricOperator G g f (preparedCutoffsAt G T hT) i y v) v ∧
    inner ℝ (scaledTargetMetricOperator G g f (preparedCutoffsAt G T hT) i y v) v ≤
      B.upper * ‖v‖ ^ 2
  map_reference : ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (j : ℕ),
    initializationMapRescaledCjNorm G g f S j K T hK (hK.trans hKT) ≤ B.map j
  metric_error : ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (j : ℕ),
    initializationMetricRescaledCjNorm G g f S j K T hK (hK.trans hKT) ≤
      B.error j * (K⁻¹ + K / T)
  map_ellipticity : ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
    B.K₀ ≤ K → B.R₀ * K ≤ T →
    ∀ (i : Fin (initializationAtlas G T (hK.trans hKT)).count) (y : EuclideanSpace ℝ (Fin n)),
    y ∈ ((initializationAtlas G T (hK.trans hKT)).chart i).target →
    ∀ v : EuclideanSpace ℝ (Fin n),
    B.mapLower * ‖v‖ ^ 2 ≤ inner ℝ
      (actualMetricOperator
        (metricInitializationMap G g f S K T hK ∘
          ((initializationAtlas G T (hK.trans hKT)).chart i).symm) y v) v ∧
    inner ℝ
      (actualMetricOperator
        (metricInitializationMap G g f S K T hK ∘
          ((initializationAtlas G T (hK.trans hKT)).chart i).symm) y v) v ≤
      B.mapUpper * ‖v‖ ^ 2
  immersion : ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
    B.K₀ ≤ K → B.R₀ * K ≤ T → ∀ x : M,
    Function.Injective (mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (metricInitializationMap G g f S K T hK) x)
  phase_margin : ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
    B.K₀ ≤ K → B.R₀ * K ≤ T →
    ∀ (i : Fin (initializationAtlas G T (hK.trans hKT)).count) (y : EuclideanSpace ℝ (Fin n)),
    y ∈ ((initializationAtlas G T (hK.trans hKT)).chart i).target →
    B.margin ≤ chartPhaseMargin
      (metricInitializationMap G g f S K T hK ∘
        ((initializationAtlas G T (hK.trans hKT)).chart i).symm) y
  phase_regular : ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T),
    B.K₀ ≤ K → B.R₀ * K ≤ T →
    PhaseRegular (metricInitializationMap G g f S K T hK) (map_smooth K T hK)

section SuccessorDimension

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M] [T2Space M] [CompactSpace M]

/-- Every reserve and every asserted property is produced for this one fixed
selector and frame. In particular no bound or margin is assumed. -/
theorem InitializationData.exists_core (data : InitializationData M m)
    (hm : 1 ≤ m)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞
      (EuclideanSpace ℝ (Fin (m+1)))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)) :
    ∃ B : InitializationReserves,
      ColoredApproximationCore data.charts g data.frame data.phase.selector B := by
  obtain ⟨value, hv, hvalue⟩ := data.exists_value_bound
  obtain ⟨degree, transition, ht, hatlas⟩ := data.exists_atlas_reference_bounds
  obtain ⟨metric, hmetric, hmrefs⟩ :=
    exists_scaledTargetMetric_derivative_bounds data.charts g data.frame
  obtain ⟨lower, upper, hl, hu, helliptic⟩ :=
    exists_scaledTargetMetric_ellipticity data.charts g data.frame
  obtain ⟨map, hmap, hmaprefs⟩ := exists_initializationMap_reference_norm_bounds
    data.charts g data.frame data.phase.selector data.phase.smooth
  obtain ⟨error, herror, herrors⟩ := exists_initializationMetric_error_norm_bounds
    data.charts g data.frame data.phase.selector data.phase.smooth data.phase.gram
  obtain ⟨margin, K₀, R₀, hmargin, hK₀, hR₀, hphase⟩ :=
    exists_metricInitializationMap_phase_margin data.charts g data.frame hm data.phase
  obtain ⟨mapLower, mapUpper, mapK₀, mapR₀, hml, hmu, hmapK₀, hmapR₀, hmapelliptic⟩ :=
    exists_metricInitializationMap_ellipticity data.charts g data.frame
      data.phase.selector data.phase.smooth data.phase.gram
  let B : InitializationReserves :=
    { value := value
      degree := degree
      transition := transition
      metric := metric
      map := map
      error := error
      lower := lower
      upper := upper
      mapLower := mapLower
      mapUpper := mapUpper
      margin := margin
      K₀ := max K₀ mapK₀
      R₀ := max R₀ mapR₀
      value_nonneg := hv
      transition_pos := ht
      metric_one_le := hmetric
      map_pos := hmap
      error_pos := herror
      lower_pos := hl
      upper_pos := hu
      mapLower_pos := hml
      mapUpper_pos := hmu
      margin_pos := hmargin
      K₀_one_le := hK₀.trans (le_max_left _ _)
      R₀_one_le := hR₀.trans (le_max_left _ _) }
  refine ⟨B, ?_⟩
  refine
    { colors_two_le := data.charts.palette_ge_two
      selector_smooth := data.phase.smooth
      selector_gram := data.phase.gram
      map_smooth := fun K T hK ↦ data.map_smooth g K T hK
      map_value := fun K T hK x ↦ hvalue g K T hK x
      atlas_smooth := fun T hT ↦ data.atlas_smooth T hT
      atlas_target := fun T hT i ↦ rfl
      atlas_buffer := fun T hT ↦ rfl
      chart_formula := fun T hT i x ↦ rfl
      inverse_chart_formula := fun T hT i y ↦ rfl
      inner_support := fun T hT i ↦
        (data.scaleFamily T hT).scaledAtlas_inner_subset_support hT i
      support_compact := fun T hT i ↦ data.atlas_support_compact T hT i
      support_degree := fun T hT ↦ (hatlas T hT).1
      transition_reference := fun T hT ↦ (hatlas T hT).2
      metric_reference := fun T hT i j y hy ↦
        (hmrefs T hT (data.scaleFamily T hT) i j y hy).2
      metric_ellipticity := fun T hT ↦ helliptic T hT (data.scaleFamily T hT)
      map_reference := hmaprefs
      metric_error := herrors
      map_ellipticity := ?_
      immersion := ?_
      phase_margin := ?_
      phase_regular := ?_ }
  · intro K T hK hKT hKK hTT i y hy v
    exact hmapelliptic K T hK hKT ((le_max_right _ _).trans hKK)
      ((mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hK)).trans hTT)
      (data.scaleFamily T (hK.trans hKT)) i y hy v
  · intro K T hK hKT hKK hTT
    apply initialization_mvfderiv_injective_of_bufferedAtlas
      _ (data.map_smooth g K T hK) (data.atlas T (hK.trans hKT)) (data.atlas_smooth T _)
    intro i y hy
    exact (hphase K T hK hKT ((le_max_left _ _).trans hKK)
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hK)).trans hTT)
      (data.scaleFamily T (hK.trans hKT)) i y hy).1
  · intro K T hK hKT hKK hTT i y hy
    exact (hphase K T hK hKT ((le_max_left _ _).trans hKK)
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hK)).trans hTT)
      (data.scaleFamily T (hK.trans hKT)) i y hy).2
  · intro K T hK hKT hKK hTT
    apply initialization_phaseRegular_of_bufferedAtlas
      (by simpa using Nat.succ_le_succ hm)
      _ (data.map_smooth g K T hK) (data.atlas T (hK.trans hKT)) (data.atlas_smooth T _)
    intro i y hy
    exact hmargin.trans_le (hphase K T hK hKT ((le_max_left _ _).trans hKK)
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hK)).trans hTT)
      (data.scaleFamily T (hK.trans hKT)) i y hy).2

end SuccessorDimension

/-- The complete actual geometric/Fréchet-norm initialization conclusion for
every n≥2, obtained solely from closedness, parallelizability and the given
smooth positive metric. No connectedness or nonemptiness is required. -/
theorem colored_approximation_core [CompactSpace M]
    (hn : 2 ≤ n)
    (hpar : IsParallelizable (M := M) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)) :
    ∃ (G : PreparedCharts M n)
      (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
      (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) →
        EuclideanSpace ℝ (Fin (closedAmbientDimension n)))
      (B : InitializationReserves), ColoredApproximationCore G g f S B := by
  cases n with
  | zero => omega
  | succ m =>
    have hm : 1 ≤ m := by omega
    obtain ⟨data⟩ := exists_initializationData (M := M) hm hpar
    obtain ⟨B, hB⟩ := data.exists_core hm g
    exact ⟨data.charts, data.frame, data.phase.selector, B, hB⟩

end GlobalEmbedding.Initialization
