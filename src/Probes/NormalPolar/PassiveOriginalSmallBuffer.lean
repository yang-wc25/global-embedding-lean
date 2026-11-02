import NormalPolar.PassiveOriginalParameterAtlas
import NormalPolar.PassiveOriginalData
import Smoothing.TensorLocalCharts

/-! A legal initial choice of a smaller common parameter buffer. The
actual charts, compact Q samples, source atlas and every native input field
are retained literally. This is an input construction performed before the
probe ball and global cutoff are chosen; it does not shrink a previously
fixed repair ball or replace the original norm domains. -/

noncomputable section
open Set Function Manifold IsManifold Metric GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {d : ℕ} {P : Type*} [TopologicalSpace P]

/-- Initial legal buffer choice; all chart and norm data stay literal. -/
def passiveOriginalSmallBuffer (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (cap : ℝ) (hcap : 0 < cap) : BufferedAtlas P (EuclideanSpace ℝ (Fin d)) where
  count := B.count
  chart := B.chart
  inner := B.inner
  inner_open := B.inner_open
  inner_subset := B.inner_subset
  cover := B.cover
  buffer := min B.buffer cap
  buffer_pos := lt_min B.buffer_pos hcap
  buffered := fun i p hp => (ball_subset_ball (min_le_left _ _)).trans (B.buffered i p hp)
  support := B.support

theorem passiveOriginalSmallBuffer_le
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (cap : ℝ) (hcap : 0 < cap) :
    (passiveOriginalSmallBuffer B cap hcap).buffer ≤ cap := min_le_right _ _

theorem passiveOriginalSmallBuffer_sampling
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (cap : ℝ) (hcap : 0 < cap)
    (i : Fin B.count) :
    bufferedSamplingCoordinates (passiveOriginalSmallBuffer B cap hcap) i ⊆
      bufferedSamplingCoordinates B i := by
  intro y hy
  obtain ⟨z,hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner,hyball⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨hzInner,(ball_subset_ball (min_le_left _ _)) hyball⟩⟩

variable [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveOriginalSmallBuffer_smooth
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (cap : ℝ) (hcap : 0 < cap) : IsSmoothBufferedAtlas (passiveOriginalSmallBuffer B cap hcap) :=
  ⟨hB.chart_mem,hB.support_subset⟩

theorem passiveOriginalSmallBuffer_samples
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (cap : ℝ) (hcap : 0 < cap)
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i) :
    ∀ i, IsCompact (Q i) ∧ Q i ⊆ ((passiveOriginalSmallBuffer B cap hcap).chart i).target ∧
      closure (bufferedSamplingCoordinates (passiveOriginalSmallBuffer B cap hcap) i) ⊆ Q i := by
  intro i
  exact ⟨(hQ i).1,(hQ i).2.1,
    (closure_mono (passiveOriginalSmallBuffer_sampling B cap hcap i)).trans (hQ i).2.2⟩

variable {n N : ℕ} {M S : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S]

/-- Literal identity of all original native fields and norm domains.
The only chosen quantity is the buffer used by the future parameter cutoff. -/
theorem passiveOriginalSmallBuffer_data
    (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (cap : ℝ) (hcap : 0 < cap)
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d))) :
    passiveOriginalData s₀ seed (passiveOriginalSmallBuffer B cap hcap) Q =
      passiveOriginalData s₀ seed B Q := rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallBuffer_samples
#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallBuffer_data
