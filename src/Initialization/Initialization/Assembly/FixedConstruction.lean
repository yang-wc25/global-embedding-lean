import Initialization.Colored.MetricMapDefinitions
import Initialization.Geometry.RescaledTransitionJets
import Initialization.Geometry.ScaledMetricGeometry
import Initialization.Phase.SelectorReference

/-!
# One actual initialization construction, fixed before both parameters

This package chooses the genuine finite chart preparation, the original global
frame, and one accepted whole-product selector. Its map is literally (7.2),
with the coframe generated from the given positive metric. The scale-T atlas
uses the same fixed chart preparation. No output map, geometry reserve or phase
margin occurs among the existence theorem's assumptions.
-/

noncomputable section
open Bundle Manifold Set Metric IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable (M : Type*) [TopologicalSpace M] (m : ℕ)
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M] [T2Space M]

/-- Construction data, whose existence is proved from compactness and the
original parallelizability assumption below. -/
structure InitializationData where
  charts : PreparedCharts M (m+1)
  frame : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) (M := M) (m+1)
  phase : @SelectorPhaseReference m (fun _ : Fin (m+1) ↦ charts.palette)
    (fun _ ↦ ⟨lt_of_lt_of_le (by decide : 0 < 2) charts.palette_ge_two⟩)

variable {M m}

/-- Fix colors and the same selector before K,T. All fields are constructed
internally, and disconnected or empty compact sources are allowed. -/
theorem exists_initializationData [CompactSpace M] (hm : 1 ≤ m)
    (hpar : IsParallelizable (M := M) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) (m+1)) :
    Nonempty (InitializationData M m) := by
  obtain ⟨G⟩ := exists_preparedCharts (M := M) (n := m+1)
  obtain ⟨f⟩ := hpar.2
  obtain ⟨P⟩ := exists_selectorPhaseReference m hm
    (fun _ : Fin (m+1) ↦ G.palette) (fun _ ↦ G.palette_ge_two)
  exact ⟨⟨G, f, P⟩⟩

namespace InitializationData

variable (data : InitializationData M m)

def map
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞
      (EuclideanSpace ℝ (Fin (m+1)))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _))
    (K T : ℝ) (hK : 1 ≤ K) :
    M → EuclideanSpace ℝ (Fin (closedAmbientDimension (m+1))) :=
  metricInitializationMap data.charts g data.frame data.phase.selector K T hK

def scaleFamily (T : ℝ) (hT : 1 ≤ T) : ChartCutoffFamily data.charts T :=
  preparedCutoffsAt data.charts T hT

def atlas (T : ℝ) (hT : 1 ≤ T) :
    BufferedAtlas M (EuclideanSpace ℝ (Fin (m+1))) :=
  (data.scaleFamily T hT).boundedAtlas hT

theorem map_smooth
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞
      (EuclideanSpace ℝ (Fin (m+1)))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _))
    (K T : ℝ) (hK : 1 ≤ K) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (closedAmbientDimension (m+1)))) ∞ (data.map g K T hK) :=
  metricInitializationMap_contMDiff data.charts g data.frame data.phase.selector data.phase.smooth K T hK

theorem exists_value_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀
      (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞
        (EuclideanSpace ℝ (Fin (m+1)))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _))
      (K T : ℝ) (hK : 1 ≤ K) (x : M), ‖data.map g K T hK x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_metricInitializationMap_value_bound
    data.charts data.phase.selector data.phase.smooth.continuous
  exact ⟨B, hB, fun g K T hK x ↦ hb g data.frame K T hK x⟩

theorem atlas_smooth (T : ℝ) (hT : 1 ≤ T) : IsSmoothBufferedAtlas (data.atlas T hT) :=
  (data.scaleFamily T hT).boundedAtlas_smooth hT

@[simp] theorem atlas_target (T : ℝ) (hT : 1 ≤ T) (i : Fin (data.atlas T hT).count) :
    ((data.atlas T hT).chart i).target = ball 0 data.charts.scaleRadius := rfl

@[simp] theorem atlas_buffer (T : ℝ) (hT : 1 ≤ T) :
    (data.atlas T hT).buffer = data.charts.scaleRadius / 2 := rfl

theorem atlas_support_compact (T : ℝ) (hT : 1 ≤ T) (i : Fin (data.atlas T hT).count) :
    IsCompact ((data.atlas T hT).support i) :=
  (data.scaleFamily T hT).enlargedSupport_compact hT i

/-- The actual fixed construction supplies its own graph-degree and all-order
transition reserves, before every real scale T. -/
theorem exists_atlas_reference_bounds [CompactSpace M] :
    ∃ (degree : ℕ) (B : ℕ → ℝ), (∀ j, 0 < B j) ∧
      ∀ T : ℝ, ∀ hT : 1 ≤ T,
        (data.atlas T hT).supportDegree ≤ degree ∧
        ∀ (i k : Fin (data.atlas T hT).count) (j : ℕ) (y : EuclideanSpace ℝ (Fin (m+1))),
          y ∈ (((data.atlas T hT).chart i).symm.trans ((data.atlas T hT).chart k)).source →
          ‖iteratedFDeriv ℝ j
            ((data.atlas T hT).chart k ∘ ((data.atlas T hT).chart i).symm) y‖ ≤ B j := by
  obtain ⟨degree, hdegree⟩ := exists_uniform_enlargedSupport_degree data.charts
  obtain ⟨B, hB, htrans⟩ := exists_uniform_boundedAtlas_transition_bounds data.charts
  exact ⟨degree, B, hB, fun T hT ↦
    ⟨hdegree T hT (data.scaleFamily T hT), htrans T hT (data.scaleFamily T hT)⟩⟩

end InitializationData
end GlobalEmbedding.Initialization
