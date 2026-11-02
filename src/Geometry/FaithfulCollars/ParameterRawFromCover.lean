import FaithfulCollars.LocalBufferedCover

/-!
# Eliminate parameter raw supply from original buffered geometric cover

The safe coordinate set is an INTERNAL geometric intersection of the
original Q_i and the pullback of the original enlarged support W_i.  All
norm conclusions continue to use the complete original Q_i.  The entire
local family and actual old RP are produced; no plateau or derivative
estimate of a desired cutoff is supplied.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {ι E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace P] [T2Space P]
  [ChartedSpace E P] [IsManifold 𝓘(ℝ, E) ∞ P]

def originalParameterSafeCoordinates
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E) (W : ι → Set P) (i : ι) : Set E :=
  Q i ∩ (chart i).symm ⁻¹' W i

def originalBufferedParameterSupportFamily
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E) (W : ι → Set P)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target) :
    TensorBufferedChartFamily ι P E :=
  originalBufferedParameterFamily chart (originalParameterSafeCoordinates chart Q W) b hb
    (fun i => inter_subset_left.trans (hQtarget i))

variable [Fintype ι]

theorem originalBufferedParameterSupportFamily_sampling
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E) (W : ι → Set P)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target) (i : ι) :
    tensorLocalSamplingCoordinates (originalBufferedParameterSupportFamily chart Q W b hb hQtarget) i ⊆ Q i :=
  (originalBufferedParameterFamily_sampling chart (originalParameterSafeCoordinates chart Q W)
    b hb (fun i => inter_subset_left.trans (hQtarget i)) i).trans inter_subset_left

theorem originalBufferedParameterSupportFamily_enlarged
    (chart : ι → OpenPartialHomeomorph P E) (Q : ι → Set E) (W : ι → Set P)
    (b : ℝ) (hb : 0 < b) (hQtarget : ∀ i, Q i ⊆ (chart i).target) :
    OriginalLocalBufferedEnlargedSupports
      (originalBufferedParameterSupportFamily chart Q W b hb hQtarget) W (b/4) := by
  intro i p hp hnear
  have h := originalBufferedParameterFamily_enlarged chart (originalParameterSafeCoordinates chart Q W)
    b hb (fun i => inter_subset_left.trans (hQtarget i)) i p hp hnear
  have hw := h.2.2
  change (chart i).symm (chart i p) ∈ W i at hw
  rwa [(chart i).left_inv hp] at hw

/-- A true local raw producer on the original parameter charts and norm
pieces. The profile precedes their finite index type and their geometry.
The only cover premise is the original BUFFERED GEOMETRIC cover of K. -/
theorem exists_uniform_parameterRaw_from_original_buffer
    (R b : ℝ) (hb : 0 < b) (T : ℕ → ℝ) (D : ℕ) :
    ∃ BP : ℕ → ℝ, (∀ j, 0 ≤ BP j) ∧
      ∀ (ι : Type*) [Fintype ι] (chart : ι → OpenPartialHomeomorph P E)
        (Q : ι → Set E) (W : ι → Set P) (K : Set P),
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ P) →
      (∀ i, Q i ⊆ (chart i).target) →
      (∀ i y, y ∈ Q i → ‖y‖ ≤ R) →
      OriginalParameterBallCover chart (originalParameterSafeCoordinates chart Q W) K b →
      (∀ i, tensorEnlargedSupportDegree W i ≤ D) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (chart p).target,
        (chart p).symm y ∈ W i → ‖iteratedFDeriv ℝ j (chart i ∘ (chart p).symm) y‖ ≤ T j) →
      ∃ B : TensorBufferedChartFamily ι P E,
        B.chart = chart ∧ (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) ∧
        ∃ raw : TensorLocalRawPreparation B K BP T D, raw.enlarged = W := by
  have hb' : 0 < b/4 := by positivity
  refine ⟨originalRefinedRawProfile E R (b/4) hb', originalRefinedRawProfile_nonneg R (b/4) hb', ?_⟩
  intro ι _ chart Q W K hchart hQtarget hRadius hcover hDegree htrans
  let B0 := originalBufferedParameterSupportFamily chart Q W b hb hQtarget
  have hB0radius : ∀ i y, y ∈ tensorLocalInner B0 i → ‖y‖ ≤ R := by
    intro i y hy
    exact hRadius i y (originalBufferedParameterSupportFamily_sampling chart Q W b hb hQtarget i
      (tensorLocalInner_subset_sampling B0 i hy))
  obtain ⟨s⟩ := originalLocalBufferedCenters_construct R (b/4) hb' B0 hB0radius
  let B := originalRefinedLocalFamily B0 R (b/4) hb' le_rfl s
  have hBsample : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i :=
    fun i => (refinedLocalFamily_sampling_subset_original B0 R (b/4) hb' le_rfl s i).trans
      (originalBufferedParameterSupportFamily_sampling chart Q W b hb hQtarget i)
  have hK : ∀ p ∈ K, ∃ i, p ∈ B0.inner i :=
    originalBufferedParameterFamily_cover chart (originalParameterSafeCoordinates chart Q W)
      b hb (fun i => inter_subset_left.trans (hQtarget i)) K hcover
  refine ⟨B, rfl, hBsample, ?_⟩
  exact ⟨localRefinedRawPreparation B0 W K R (b/4) hb' le_rfl s hchart hK
    (originalBufferedParameterSupportFamily_enlarged chart Q W b hb hQtarget) T D hDegree htrans, rfl⟩

end GlobalEmbedding.Continuation.FaithfulCollars
