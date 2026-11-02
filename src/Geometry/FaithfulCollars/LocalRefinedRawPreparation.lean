import FaithfulCollars.LocalBufferedCenters
import FaithfulCollars.RefinedRawPreparation
import Smoothing.TensorLocalPrepared

/-!
# General local raw supply from the original buffered cover of K

This version removes the centered-ball assumption of LocalRawPreparation.
The original local family may have arbitrary open coordinate inners.  A
bounded finite separated-center family is constructed internally and then
collapsed into one literal plateau per ORIGINAL chart.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {ι E P : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace P] [T2Space P]
  [ChartedSpace E P] [IsManifold 𝓘(ℝ, E) ∞ P]

def OriginalLocalBufferedEnlargedSupports
    (B : TensorBufferedChartFamily ι P E) (W : ι → Set P) (b : ℝ) : Prop :=
  ∀ i p, p ∈ (B.chart i).source →
    (∃ c ∈ tensorLocalInner B i, dist (B.chart i p) c ≤ b/4) → p ∈ W i

def originalLocalRefinedRaw (B : TensorBufferedChartFamily ι P E)
    (R b : ℝ) (hb : 0 < b) (s : OriginalLocalBufferedCenters B R b hb)
    (i : ι) : P → ℝ :=
  chartCenterRaw (B.chart i) (s.centers i) (b/8)

def localRefinedRawPreparation
    (B : TensorBufferedChartFamily ι P E) (W : ι → Set P) (K : Set P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ B.buffer)
    (s : OriginalLocalBufferedCenters B R b hb)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ P)
    (hK : ∀ p ∈ K, ∃ i, p ∈ B.inner i)
    (hEnlarged : OriginalLocalBufferedEnlargedSupports B W b)
    (T : ℕ → ℝ) (D : ℕ) (hD : ∀ i, tensorEnlargedSupportDegree W i ≤ D)
    (htrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (B.chart p).target,
      (B.chart p).symm y ∈ W i →
      ‖iteratedFDeriv ℝ j (B.chart i ∘ (B.chart p).symm) y‖ ≤ T j) :
    TensorLocalRawPreparation (originalRefinedLocalFamily B R b hb hbuffer s) K
      (originalRefinedRawProfile E R b hb) T D := by
  have hcompact (i : ι) := chartCenterRaw_compact_support (B.chart i)
    (s.centers i) (b/8) (by positivity) (s.separated i)
    (localRefinedWorkingCarrier_target B R b hb hbuffer s i)
  have hlarge (i : ι) : tsupport (originalLocalRefinedRaw B R b hb s i) ⊆ W i := by
    intro p hp
    have h := (hcompact i).2 hp
    apply hEnlarged i p h.1
    obtain ⟨c, hc⟩ := mem_iUnion.mp h.2
    exact ⟨c.val, s.center_inner i c.property, by
      have hc' : dist (B.chart i p) c.val ≤ 2*(b/8) := hc
      linarith⟩
  refine {
    raw := originalLocalRefinedRaw B R b hb s
    smooth := ?_
    plateau_on := ?_
    inner_support := ?_
    enlarged := W
    enlarged_support := hlarge
    degree := hD
    own_jets := ?_
    transition_jets := ?_ }
  · intro i
    exact chartCenterRaw_smooth (B.chart i) (hB i) (s.centers i) (b/8)
      (by positivity) (s.separated i) (localRefinedWorkingCarrier_target B R b hb hbuffer s i)
  · intro p hp
    obtain ⟨i, hi⟩ := hK p hp
    exact ⟨i, chartCenterRaw_one_on (B.chart i) (s.centers i) (b/8) (by positivity)
      (tensorLocalInner B i) (s.covers i)
      (B.inner_subset i hi) (tensorLocalInner_mem B i hi)⟩
  · intro i p hp
    have h := (hcompact i).2 hp
    exact ⟨h.1, localRefinedWorkingCarrier_domain B R b hb s i h.2⟩
  · intro i j y hy
    exact chartCenterRaw_own_jets (B.chart i) (s.centers i) (b/8) (by positivity)
      (sourceCollarNovPieceBound E R b hb) (s.count_le i) (s.separated i) j y hy
  · intro p i j hj y hy hx
    exact htrans p i j hj y hy (hlarge i hx)

/-- The profile precedes the arbitrary finite local chart family, including
its index type. The centers and actual old RP are constructed as outputs.
The covering hypothesis concerns original chart sets only. -/
theorem exists_uniform_localRefinedRawPreparation
    (R b : ℝ) (hb : 0 < b) (T : ℕ → ℝ) (D : ℕ) :
    ∃ BP : ℕ → ℝ, (∀ j, 0 ≤ BP j) ∧
      ∀ (ι : Type*) [Fintype ι] (B : TensorBufferedChartFamily ι P E)
        (W : ι → Set P) (K : Set P),
      (∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ P) →
      b ≤ B.buffer →
      (∀ i y, y ∈ tensorLocalInner B i → ‖y‖ ≤ R) →
      (∀ p ∈ K, ∃ i, p ∈ B.inner i) →
      OriginalLocalBufferedEnlargedSupports B W b →
      (∀ i, tensorEnlargedSupportDegree W i ≤ D) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (B.chart p).target,
        (B.chart p).symm y ∈ W i →
        ‖iteratedFDeriv ℝ j (B.chart i ∘ (B.chart p).symm) y‖ ≤ T j) →
      ∃ s : OriginalLocalBufferedCenters B R b hb,
        ∃ hbuffer : b ≤ B.buffer,
        ∃ raw : TensorLocalRawPreparation (originalRefinedLocalFamily B R b hb hbuffer s) K BP T D,
          raw.raw = originalLocalRefinedRaw B R b hb s := by
  refine ⟨originalRefinedRawProfile E R b hb, originalRefinedRawProfile_nonneg R b hb, ?_⟩
  intro ι _ B W K hB hbuffer hRadius hK hEnlarged hD htrans
  obtain ⟨s⟩ := originalLocalBufferedCenters_construct R b hb B hRadius
  exact ⟨s, hbuffer, localRefinedRawPreparation B W K R b hb hbuffer s hB hK hEnlarged T D hD htrans, rfl⟩

end GlobalEmbedding.Continuation.FaithfulCollars
