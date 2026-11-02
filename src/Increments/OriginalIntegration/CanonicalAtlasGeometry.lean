import OriginalIntegration.OriginalRepairGeometry
import FaithfulCollars.InitializationBridge
import Initialization.Geometry.RescaledTransitionJets
import Initialization.Assembly.RescaledNorms
import Smoothing.Round4ParameterEtaTransfer

/-!
# Original geometry of the actual canonical scale atlases

The same initialization atlas, its full open chart targets and original
enlarged supports supply every primitive geometric repair field. Constants
come from fixed prepared parent charts before either real scale or either
resulting chart count. All raw, compact carrier and collar objects can then
be manufactured by `OriginalRepairGeometry.actual_compact_supply`.

In particular, these are literal original open norm domains. No compactness
of an original target ball and no desired repair estimate is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Initialization
  Set Function Manifold IsManifold Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulCollars

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]

def originalCanonicalTransitionProfile (G : PreparedCharts M n) : ℕ → ℝ :=
  (exists_uniform_boundedAtlas_transition_bounds G).choose

theorem originalCanonicalTransitionProfile_pos (G : PreparedCharts M n) (j : ℕ) :
    0 < originalCanonicalTransitionProfile G j :=
  (exists_uniform_boundedAtlas_transition_bounds G).choose_spec.1 j

theorem originalCanonicalTransitionProfile_bound
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T)
    (i k : Fin (initializationAtlas G T hT).count) (j : ℕ)
    (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (((initializationAtlas G T hT).chart i).symm.trans
      ((initializationAtlas G T hT).chart k)).source) :
    ‖iteratedFDeriv ℝ j ((initializationAtlas G T hT).chart k ∘
      ((initializationAtlas G T hT).chart i).symm) y‖ ≤ originalCanonicalTransitionProfile G j :=
  (exists_uniform_boundedAtlas_transition_bounds G).choose_spec.2
    T hT (preparedCutoffsAt G T hT) i k j y hy

def originalCanonicalSupportDegree (G : PreparedCharts M n) : ℕ :=
  (exists_uniform_enlargedSupport_degree G).choose

theorem originalCanonicalSupportDegree_bound
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T) :
    (initializationAtlas G T hT).supportDegree ≤ originalCanonicalSupportDegree G :=
  (exists_uniform_enlargedSupport_degree G).choose_spec T hT (preparedCutoffsAt G T hT)

theorem originalCanonicalAtlas_smooth
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T) :
    IsSmoothBufferedAtlas (initializationAtlas G T hT) :=
  (preparedCutoffsAt G T hT).boundedAtlas_smooth hT

theorem originalCanonicalAtlas_norm_buffer
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T) :
    OriginalSourceNormBuffer (initializationAtlas G T hT)
      (fun i => ((initializationAtlas G T hT).chart i).target)
      G.scaleRadius (G.scaleRadius/10) := by
  apply originalSourceNormBuffer_of_fixed_balls _ _ G.scaleRadius G.scaleRadius
    (initialization_boundedAtlas_fixed_ball_geometry (preparedCutoffsAt G T hT) hT)
    (fun _ => Subset.rfl)
  · intro i y hy
    exact le_of_lt (by simpa only [initializationAtlas,
      ChartCutoffFamily.boundedAtlas_target, mem_ball, dist_zero_right] using hy)
  · intro i
    change ball (0 : EuclideanSpace ℝ (Fin n)) (G.scaleRadius/4) ⊆ ball 0 G.scaleRadius
    exact ball_subset_ball (by linarith [G.scaleRadius_pos])

theorem originalCanonicalAtlas_parameter_buffer
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T) :
    OriginalParameterNormBuffer (initializationAtlas G T hT).chart
      (fun i => ((initializationAtlas G T hT).chart i).target)
      (initializationAtlas G T hT).support univ G.scaleRadius (G.scaleRadius/10) := by
  let g := initialization_boundedAtlas_fixed_ball_geometry (preparedCutoffsAt G T hT) hT
  apply originalParameterNormBuffer_of_fixed_balls _ _ _ univ G.scaleRadius G.scaleRadius
    (originalLocalGeometry_of_fixedBallAtlas _ _ g univ) (fun _ => Subset.rfl)
  · intro i y hy
    exact (originalCanonicalAtlas_norm_buffer G T hT).norm_radius i y hy
  · intro i
    change ball (0 : EuclideanSpace ℝ (Fin n)) (G.scaleRadius/4) ⊆ ball 0 G.scaleRadius
    exact ball_subset_ball (by linarith [G.scaleRadius_pos])
  · exact g.enlarged_support

theorem originalCanonicalAtlas_raw_transition
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T)
    (p i : Fin (initializationAtlas G T hT).count) (j : ℕ) (_hj : 1 ≤ j)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ((initializationAtlas G T hT).chart p).target)
    (hi : ((initializationAtlas G T hT).chart p).symm y ∈ (initializationAtlas G T hT).support i) :
    ‖iteratedFDeriv ℝ j ((initializationAtlas G T hT).chart i ∘
      ((initializationAtlas G T hT).chart p).symm) y‖ ≤ originalCanonicalTransitionProfile G j :=
  originalCanonicalTransitionProfile_bound G T hT p i j y
    ⟨hy,(originalCanonicalAtlas_smooth G T hT).support_subset i hi⟩

variable {d : ℕ}

theorem originalCanonicalAtlas_spatial_joint
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T) :
    OriginalSpatialJointTransitions (d := d) (initializationAtlas G T hT)
      (fun i => ((initializationAtlas G T hT).chart i).target)
      (fun j => max 1 (originalCanonicalTransitionProfile G j)) := by
  intro i j k hk z _ hOverlap
  let A := initializationAtlas G T hT
  let e := (A.chart i).symm.trans (A.chart j)
  have he : ContDiffOn ℝ ∞ e e.source :=
    (round3Parameter_partial_trans_smooth (A.chart i).symm (A.chart j)
      (contMDiffOn_symm_of_mem_maximalAtlas ((originalCanonicalAtlas_smooth G T hT).chart_mem i))
      (contMDiffOn_of_mem_maximalAtlas ((originalCanonicalAtlas_smooth G T hT).chart_mem j))).contDiffOn
  exact tensor_product_map_jet_le isOpen_univ e.open_source contDiff_id.contDiffOn he
    (mem_univ z.1) hOverlap.2 k 1 (originalCanonicalTransitionProfile G k)
    (round4_positive_identity_jet_norm_le k hk z.1)
    (originalCanonicalTransitionProfile_bound G T hT i j k z.2 hOverlap.2)

theorem originalCanonicalAtlas_parameter_joint
    (G : PreparedCharts M n) (T : ℝ) (hT : 1 ≤ T) :
    OriginalParameterJointTransitions (n := d) (initializationAtlas G T hT).chart
      (fun i => ((initializationAtlas G T hT).chart i).target)
      (fun j => max (originalCanonicalTransitionProfile G j) 1) := by
  intro i j k hk z _ hOverlap
  let A := initializationAtlas G T hT
  let e := (A.chart i).symm.trans (A.chart j)
  have he : ContDiffOn ℝ ∞ e e.source :=
    (round3Parameter_partial_trans_smooth (A.chart i).symm (A.chart j)
      (contMDiffOn_symm_of_mem_maximalAtlas ((originalCanonicalAtlas_smooth G T hT).chart_mem i))
      (contMDiffOn_of_mem_maximalAtlas ((originalCanonicalAtlas_smooth G T hT).chart_mem j))).contDiffOn
  exact tensor_product_map_jet_le e.open_source isOpen_univ he contDiff_id.contDiffOn
    hOverlap.1 (mem_univ z.2) k (originalCanonicalTransitionProfile G k) 1
    (originalCanonicalTransitionProfile_bound G T hT i j k z.1 hOverlap.1)
    (round4_positive_identity_jet_norm_le k hk z.2)

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.originalCanonicalAtlas_norm_buffer
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.originalCanonicalAtlas_spatial_joint
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.originalCanonicalAtlas_parameter_joint
