import OriginalIntegration.OriginalRepairGeometry
import FaithfulCollars.OriginalChartReindex

/-! Internal compact carriers and finite index casts preserve the original
reference bounds and return the same actual repair limit to the original
public chart index set.  These are exact identities or proved restrictions,
not replacement norm assumptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Filter
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulCollars

variable {b : OriginalRepairGeometryBudget} {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

variable (g : OriginalRepairGeometry b n d M P) (c : SourceCollarNovSetup n d M P)
  (hs : c.source.count = g.atlas.count) (hp : c.parameter.count = g.parameterCount)
  (hS : ∀ i, c.source.chart i = g.atlas.chart (Fin.cast hs i))
  (hP : ∀ i, c.parameter.chart i = g.parameterChart (Fin.cast hp i))
  (hOmega : ∀ i, c.Omega i ⊆ g.Omega (Fin.cast hs i))
  (hQ : ∀ i, c.Q i ⊆ g.Q (Fin.cast hp i))

include hS hP hOmega hQ

theorem internal_map_norm_le_original (F : P × M → EuclideanSpace ℝ (Fin N)) (j : ℕ) :
    paperAtlasCj j (incrementsOriginalMapCoordinates c.source c.parameter.chart F)
      c.differentiation c.samples ≤
    paperAtlasCj j (incrementsOriginalMapCoordinates g.atlas g.parameterChart F)
      g.differentiation g.samples := by
  have h := paperAtlasCj_mono_evaluation j
    (incrementsOriginalMapCoordinates c.source c.parameter.chart F) c.differentiation c.samples
    (incrementsOriginalEvaluation c.source c.parameter.chart
      (fun i => g.Omega (Fin.cast hs i)) (fun i => g.Q (Fin.cast hp i)) univ)
    (fun i y hy => ⟨hy.1,hOmega i.1 hy.2.1,hQ i.2 hy.2.2.1,hy.2.2.2⟩)
  exact h.trans_eq (originalMapCj_cast g.atlas c.source g.parameterChart c.parameter.chart
    hs hp hS hP g.Omega g.Q univ F j)

theorem internal_tensor_norm_le_original
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)) (j : ℕ) :
    paperAtlasCj j (incrementsOriginalTensorCoordinates c.source c.parameter.chart T)
      c.differentiation c.samples ≤
    paperAtlasCj j (incrementsOriginalTensorCoordinates g.atlas g.parameterChart T)
      g.differentiation g.samples := by
  have h := paperAtlasCj_mono_evaluation j
    (incrementsOriginalTensorCoordinates c.source c.parameter.chart T) c.differentiation c.samples
    (incrementsOriginalEvaluation c.source c.parameter.chart
      (fun i => g.Omega (Fin.cast hs i)) (fun i => g.Q (Fin.cast hp i)) univ)
    (fun i y hy => ⟨hy.1,hOmega i.1 hy.2.1,hQ i.2 hy.2.2.1,hy.2.2.2⟩)
  exact h.trans_eq (originalTensorCj_cast g.atlas c.source g.parameterChart c.parameter.chart
    hs hp hS hP g.Omega g.Q univ T j)

omit hOmega hQ in
theorem original_parameter_transition_under_cast :
    OriginalParameterJointTransitions (n := n) c.parameter.chart
      (fun i => g.Q (Fin.cast hp i)) b.parameterTransition := by
  intro i j k hk z hz ho
  rw [hP i,hP j] at ho ⊢
  exact g.parameter_transition (Fin.cast hp i) (Fin.cast hp j) k hk z hz ho

omit hOmega hQ in
theorem original_spatial_transition_under_cast :
    OriginalSpatialJointTransitions (d := d) c.source
      (fun i => g.Omega (Fin.cast hs i)) b.spatialTransition := by
  intro i j k hk z hz ho
  rw [hS i,hS j] at ho ⊢
  exact g.spatial_transition (Fin.cast hs i) (Fin.cast hs j) k hk z hz ho

omit hOmega hQ in
theorem original_tensor_smooth_under_cast
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (hT : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates g.atlas g.parameterChart T i)
      (g.differentiation i)) :
    ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates c.source c.parameter.chart T i)
      (c.differentiation i) := by
  intro i
  rw [originalTensorCoordinates_cast g.atlas c.source g.parameterChart c.parameter.chart hs hp hS hP T i]
  change ContDiffOn ℝ ∞ _ (incrementsOriginalDifferentiation c.source c.parameter.chart i)
  rw [originalDifferentiation_cast g.atlas c.source g.parameterChart c.parameter.chart hs hp hS hP i]
  exact hT (Fin.cast hs i.1,Fin.cast hp i.2)

end GlobalEmbedding.Continuation.OriginalIntegration

namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulCollars
variable {b : OriginalRepairGeometryBudget} {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem original_repair_conclusion_reindex
    (g : OriginalRepairGeometry b (m+1) d M P) (c : SourceCollarNovSetup (m+1) d M P)
    (hs : c.source.count = g.atlas.count) (hp : c.parameter.count = g.parameterCount)
    (hS : ∀ i, c.source.chart i = g.atlas.chart (Fin.cast hs i))
    (hP : ∀ i, c.parameter.chart i = g.parameterChart (Fin.cast hp i))
    {F0 Fstar : P × M → V}
    {metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)}
    {rho t0 : ℝ} {G u : ℕ → P × M → V} {stage : ℕ → ℕ}
    (out : OriginalRepairConclusion c.source c.parameter.chart
      (fun i => g.Omega (Fin.cast hs i)) (fun i => g.Q (Fin.cast hp i))
      F0 metric rho t0 Fstar G u stage) :
    OriginalRepairConclusion g.atlas g.parameterChart g.Omega g.Q
      F0 metric rho t0 Fstar G u stage := by
  have hCj (F : P × M → V) (j : ℕ) :=
    originalMapCj_cast g.atlas c.source g.parameterChart c.parameter.chart hs hp hS hP
      g.Omega g.Q univ F j
  refine {
    initial := out.initial
    maps_smooth := out.maps_smooth
    increments_smooth := out.increments_smooth
    actual_update := out.actual_update
    stage_min := out.stage_min
    stage_step := out.stage_step
    stages := out.stages
    summable := out.summable
    same_series := out.same_series
    joint_smooth := out.joint_smooth
    slice_smooth := out.slice_smooth
    exact_metric := out.exact_metric
    slice_immersion := out.slice_immersion
    phase_regular := out.phase_regular
    strict_C2 := by rw [← hCj]; exact out.strict_C2
    original_norms := ?_
    original_jets := ?_ }
  · intro a
    simpa only [hCj] using out.original_norms a
  · intro i a y hy
    let e := originalChartIndexEquiv g.atlas c.source hs hp
    let i' := e.symm i
    have hi : (Fin.cast hs i'.1,Fin.cast hp i'.2) = i := e.apply_symm_apply i
    have hDiff := originalDifferentiation_cast g.atlas c.source g.parameterChart c.parameter.chart
      hs hp hS hP i'
    rw [hi] at hDiff
    have hMap (F : P × M → V) := originalMapCoordinates_cast g.atlas c.source
      g.parameterChart c.parameter.chart hs hp hS hP F i'
    simp only [hi] at hMap
    have h := out.original_jets i' a y (hDiff.symm ▸ hy)
    simpa only [hMap] using h

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.internal_map_norm_le_original
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.internal_tensor_norm_le_original
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_repair_conclusion_reindex
