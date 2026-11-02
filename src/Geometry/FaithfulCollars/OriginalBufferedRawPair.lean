import FaithfulCollars.OriginalNormBufferGeometry

/-!
# Source and parameter raw families manufactured together

The original numerical radii and transition bounds select both own-chart
jet profiles BEFORE either atlas, its cardinality or the parameter index.
The actual centers, working source atlas, local parameter family and both
raw preparations are then constructed from the primitive buffered geometry.

The original `Omega`, `Q`, chart functions, source enlarged supports and
parameter enlarged supports remain unchanged.  Only the internal source
inner sets and buffer, and an internal parameter inner family, are chosen
for the older smoothing consumers.  No raw/partition/collar field appears
among the hypotheses.  This is the general buffered-chart version of the
earlier fixed-ball-only raw pair.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E F M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace P] [T2Space P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P]

/-- Full actual raw supply at one source/parameter numerical class.  There
is one pair of preparations, and each contains estimates at every order. -/
theorem exists_uniform_originalBufferedRawPair
    (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP : ℕ → ℝ) (Ds Dp : ℕ) :
    ∃ BS BP : ℕ → ℝ, (∀ j, 0 ≤ BS j) ∧ (∀ j, 0 ≤ BP j) ∧
      ∀ (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
        (gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
        (ι : Type*) [Fintype ι]
        (chart : ι → OpenPartialHomeomorph P F) (Q : ι → Set F)
        (W : ι → Set P) (K : Set P)
        (gP : OriginalParameterNormBuffer chart Q W K RPar bPar),
      IsSmoothBufferedAtlas A →
      (∀ i, chart i ∈ maximalAtlas 𝓘(ℝ,F) ∞ P) →
      A.supportDegree ≤ Ds →
      (∀ i, tensorEnlargedSupportDegree W i ≤ Dp) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (A.chart p).target,
        (A.chart p).symm y ∈ A.support i →
        ‖iteratedFDeriv ℝ j (A.chart i ∘ (A.chart p).symm) y‖ ≤ TS j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (chart p).target,
        (chart p).symm y ∈ W i →
        ‖iteratedFDeriv ℝ j (chart i ∘ (chart p).symm) y‖ ≤ TP j) →
      let A0 := originalNormBufferedAtlas A bSrc hbSrc gS.chart_buffer
      ∃ s : SourceCollarNovFamily A0 Omega RSrc bSrc hbSrc,
        let AS := originalRefinedWorkingAtlas A0 Omega RSrc bSrc hbSrc le_rfl s
        AS.chart = A.chart ∧ AS.support = A.support ∧ AS.supportDegree = A.supportDegree ∧
        IsSmoothBufferedAtlas AS ∧
        (∀ i, bufferedSamplingCoordinates AS i ⊆ Omega i) ∧
        (∀ i x, x ∈ AS.inner i → A.chart i x ∈ Omega i) ∧
        ∃ AP : TensorBufferedChartFamily ι P F,
          AP.chart = chart ∧ (∀ i, tensorLocalSamplingCoordinates AP i ⊆ Q i) ∧
          ∃ rawS : TensorRawCutoffPreparation AS BS TS Ds,
            ∃ rawP : TensorLocalRawPreparation AP K BP TP Dp,
              rawS.raw = originalRefinedRaw A0 Omega RSrc bSrc hbSrc s ∧
              rawP.enlarged = W := by
  obtain ⟨BS, hBS, hSource⟩ := exists_uniform_refinedRawPreparation
    (M := M) (E := E) RSrc bSrc hbSrc TS Ds
  obtain ⟨BP, hBP, hParameter⟩ := exists_uniform_parameterRaw_from_original_buffer
    (P := P) (E := F) RPar bPar hbPar TP Dp
  refine ⟨BS, BP, hBS, hBP, ?_⟩
  intro A Omega gS ι _ chart Q W K gP hA hChart hDs hDp hSTrans hPTrans
  let A0 := originalNormBufferedAtlas A bSrc hbSrc gS.chart_buffer
  have hA0 : IsSmoothBufferedAtlas A0 := ⟨hA.chart_mem, hA.support_subset⟩
  have hSample0 : ∀ i, bufferedSamplingCoordinates A0 i ⊆ Omega i :=
    gS.original_sampling
  have hLarge0 : OriginalBufferedEnlargedSupports A0 bSrc := gS.enlarged_buffer
  obtain ⟨s, hbuffer, rawS, hRawS⟩ :=
    hSource A0 Omega hA0 le_rfl hSample0 gS.norm_radius hLarge0 hDs hSTrans
  let AS := originalRefinedWorkingAtlas A0 Omega RSrc bSrc hbSrc le_rfl s
  have hSampleS : ∀ i, bufferedSamplingCoordinates AS i ⊆ Omega i :=
    fun i => (refinedWorkingAtlas_sampling_subset_original A0 Omega RSrc bSrc hbSrc
      le_rfl s i).trans (hSample0 i)
  obtain ⟨AP, hAPchart, hAPsample, rawP, hRawP⟩ := hParameter ι chart Q W K
    hChart gP.norm_target gP.norm_radius gP.safe_ball_cover hDp hPTrans
  refine ⟨s, rfl, rfl, rfl, refinedWorkingAtlas_smooth A0 Omega RSrc bSrc hbSrc
    le_rfl s hA0, hSampleS, ?_, AP, hAPchart, hAPsample, rawS, rawP, hRawS, hRawP⟩
  intro i x hx
  exact hSampleS i (bufferedInner_subset_sampling AS i (bufferedInnerCoordinates_mem AS i hx))

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.exists_uniform_originalBufferedRawPair
