import FaithfulCollars.RefinedWorkingAtlas
import Smoothing.TensorPreparedProduct

/-!
# Raw production from general original bounded buffered charts

The original inner need not be a ball and its coordinates need not be
centered at zero.  Its original finite bounded-center refinement is
manufactured internally, and the center cutoffs are summed to retain one
raw function per ORIGINAL chart.  The profile depends on the fixed radius
and buffer, not on chart count, chosen centers or actual atlas.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def originalRefinedRaw (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
    (R b : ℝ) (hb : 0 < b) (s : SourceCollarNovFamily A Omega R b hb)
    (i : Fin A.count) : M → ℝ :=
  chartCenterRaw (A.chart i) (s.centers i) (b/8)

def originalRefinedRawProfile (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (R b : ℝ) (hb : 0 < b) : ℕ → ℝ :=
  centerRawProfile E (b/8) (by positivity) (sourceCollarNovPieceBound E R b hb)

theorem originalRefinedRawProfile_nonneg (R b : ℝ) (hb : 0 < b) (j : ℕ) :
    0 ≤ originalRefinedRawProfile E R b hb j :=
  centerRawProfile_nonneg E (b/8) (by positivity) (sourceCollarNovPieceBound E R b hb) j

def refinedRawPreparation
    (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ A.buffer)
    (s : SourceCollarNovFamily A Omega R b hb) (hA : IsSmoothBufferedAtlas A)
    (hEnlarged : OriginalBufferedEnlargedSupports A b)
    (T : ℕ → ℝ) (D : ℕ) (hD : A.supportDegree ≤ D)
    (htrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ A.support i →
      ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ T j) :
    TensorRawCutoffPreparation (originalRefinedWorkingAtlas A Omega R b hb hbuffer s)
      (originalRefinedRawProfile E R b hb) T D := by
  have hcompact (i : Fin A.count) := chartCenterRaw_compact_support (A.chart i)
    (s.centers i) (b/8) (by positivity) (s.separated i)
    (refinedWorkingCarrier_target A Omega R b hb s i)
  have hlarge (i : Fin A.count) : tsupport (originalRefinedRaw A Omega R b hb s i) ⊆ A.support i := by
    intro x hx
    have h := (hcompact i).2 hx
    apply hEnlarged i x h.1
    obtain ⟨c, hc⟩ := mem_iUnion.mp h.2
    exact ⟨c.val, s.center_inner i c.property, by
      have hc' : dist (A.chart i x) c.val ≤ 2*(b/8) := hc
      linarith⟩
  refine {
    raw := originalRefinedRaw A Omega R b hb s
    smooth := ?_
    plateau_cover := ?_
    inner_support := ?_
    enlarged_support := hlarge
    degree := hD
    own_jets := ?_
    transition_jets := ?_ }
  · intro i
    exact chartCenterRaw_smooth (A.chart i) (hA.chart_mem i) (s.centers i) (b/8)
      (by positivity) (s.separated i) (refinedWorkingCarrier_target A Omega R b hb s i)
  · intro x
    obtain ⟨i, hi⟩ := A.cover x
    exact ⟨i, chartCenterRaw_one_on (A.chart i) (s.centers i) (b/8) (by positivity)
      (bufferedInnerCoordinates A i) (s.covers i)
      (A.inner_subset i hi) (bufferedInnerCoordinates_mem A i hi)⟩
  · intro i x hx
    have h := (hcompact i).2 hx
    exact ⟨h.1, refinedWorkingCarrier_domain A Omega R b hb s i h.2⟩
  · intro i j y hy
    exact chartCenterRaw_own_jets (A.chart i) (s.centers i) (b/8) (by positivity)
      (sourceCollarNovPieceBound E R b hb) (s.count_le i) (s.separated i) j y hy
  · intro p i j hj y hy hx
    exact htrans p i j hj y hy (hlarge i hx)

/-- The original finite-radius setup produces the actual raw preparation.
No center family, raw function, normalized cutoff, or collar is an input.
The geometry constants are fixed before ANY actual atlas. -/
theorem exists_uniform_refinedRawPreparation
    (R b : ℝ) (hb : 0 < b) (T : ℕ → ℝ) (D : ℕ) :
    ∃ BS : ℕ → ℝ, (∀ j, 0 ≤ BS j) ∧
      ∀ (A : BufferedAtlas M E) (Omega : Fin A.count → Set E),
      IsSmoothBufferedAtlas A → b ≤ A.buffer →
      (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
      (∀ i y, y ∈ Omega i → ‖y‖ ≤ R) →
      OriginalBufferedEnlargedSupports A b → A.supportDegree ≤ D →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ A.support i →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ T j) →
      ∃ s : SourceCollarNovFamily A Omega R b hb,
        ∃ hbuffer : b ≤ A.buffer,
        ∃ raw : TensorRawCutoffPreparation
          (originalRefinedWorkingAtlas A Omega R b hb hbuffer s) BS T D,
          raw.raw = originalRefinedRaw A Omega R b hb s := by
  refine ⟨originalRefinedRawProfile E R b hb, originalRefinedRawProfile_nonneg R b hb, ?_⟩
  intro A Omega hA hbuffer hSampling hRadius hEnlarged hD htrans
  obtain ⟨s⟩ := sourceCollarNov_construct R b hb A Omega hbuffer hSampling hRadius
  exact ⟨s, hbuffer, refinedRawPreparation A Omega R b hb hbuffer s hA hEnlarged T D hD htrans, rfl⟩

end GlobalEmbedding.Continuation.FaithfulCollars
