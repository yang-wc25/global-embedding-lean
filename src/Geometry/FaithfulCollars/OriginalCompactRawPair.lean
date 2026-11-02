import FaithfulCollars.CompactSamplingCarriers

/-!
# Actual raw pair and compact internal geometry on unchanged open norms

This strengthens the primitive buffered supplier with the compact
internal carriers needed by repair.  Compactness of the ORIGINAL `Omega`
or `Q` is not a premise or conclusion.  Each manufactured carrier lies
inside that original norm set and contains actual sampling.  All raw
functions, charts and enlarged supports retain the previous formulas.
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

theorem exists_uniform_originalCompactRawPair
    (RSrc bSrc RPar bPar : ℝ) (hbSrc : 0 < bSrc) (hbPar : 0 < bPar)
    (TS TP : ℕ → ℝ) (Ds Dp : ℕ) :
    ∃ BS BP : ℕ → ℝ, (∀ j, 0 ≤ BS j) ∧ (∀ j, 0 ≤ BP j) ∧
      ∀ (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
        (gS : OriginalSourceNormBuffer A Omega RSrc bSrc)
        (ι : Type*) [Fintype ι]
        (chart : ι → OpenPartialHomeomorph P F) (Q : ι → Set F)
        (W : ι → Set P) (K : Set P)
        (_gP : OriginalParameterNormBuffer chart Q W K RPar bPar),
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
        IsSmoothBufferedAtlas AS ∧ CompactSpace M ∧
        ∃ (AP : TensorBufferedChartFamily ι P F)
          (KS : Fin A.count → Set E) (KP : ι → Set F),
          AP.chart = chart ∧ AP.buffer = bPar/32 ∧
          (∀ i, IsCompact (KS i) ∧ KS i ⊆ Omega i) ∧
          (∀ i, IsCompact (KP i) ∧ KP i ⊆ Q i) ∧
          (∀ i, bufferedSamplingCoordinates AS i ⊆ KS i) ∧
          (∀ i, tensorLocalSamplingCoordinates AP i ⊆ KP i) ∧
          ∃ rawS : TensorRawCutoffPreparation AS BS TS Ds,
            ∃ rawP : TensorLocalRawPreparation AP K BP TP Dp,
              rawS.raw = originalRefinedRaw A0 Omega RSrc bSrc hbSrc s ∧
              rawP.enlarged = W ∧
              (∀ i, HasCompactSupport (rawS.raw i)) ∧
              (∀ i, HasCompactSupport (rawP.raw i)) := by
  have hbPar' : 0 < bPar/4 := by positivity
  refine ⟨originalRefinedRawProfile E RSrc bSrc hbSrc,
    originalRefinedRawProfile F RPar (bPar/4) hbPar',
    originalRefinedRawProfile_nonneg RSrc bSrc hbSrc,
    originalRefinedRawProfile_nonneg RPar (bPar/4) hbPar', ?_⟩
  intro A Omega gS ι _ chart Q W K gP hA hChart hDs hDp hSTrans hPTrans
  let A0 := originalNormBufferedAtlas A bSrc hbSrc gS.chart_buffer
  have hA0 : IsSmoothBufferedAtlas A0 := ⟨hA.chart_mem, hA.support_subset⟩
  have hSample0 : ∀ i, bufferedSamplingCoordinates A0 i ⊆ Omega i := gS.original_sampling
  obtain ⟨s⟩ := sourceCollarNov_construct RSrc bSrc hbSrc A0 Omega le_rfl hSample0 gS.norm_radius
  let AS := originalRefinedWorkingAtlas A0 Omega RSrc bSrc hbSrc le_rfl s
  let KS := sourceRefinedSamplingCarrier A0 Omega RSrc bSrc hbSrc s
  have hKS (i) : IsCompact (KS i) ∧ KS i ⊆ Omega i :=
    ⟨sourceRefinedSamplingCarrier_compact A0 Omega RSrc bSrc hbSrc s i,
      sourceRefinedSamplingCarrier_original A0 Omega RSrc bSrc hbSrc le_rfl s hSample0 i⟩
  have hSampleS : ∀ i, bufferedSamplingCoordinates AS i ⊆ KS i :=
    refinedWorkingAtlas_sampling_subset_carrier A0 Omega RSrc bSrc hbSrc le_rfl s
  let rawS := refinedRawPreparation A0 Omega RSrc bSrc hbSrc le_rfl s hA0
    gS.enlarged_buffer TS Ds hDs hSTrans
  let B0 := originalBufferedParameterSupportFamily chart Q W bPar hbPar gP.norm_target
  have hB0sample : ∀ i, tensorLocalSamplingCoordinates B0 i ⊆ Q i :=
    originalBufferedParameterSupportFamily_sampling chart Q W bPar hbPar gP.norm_target
  have hB0radius : ∀ i y, y ∈ tensorLocalInner B0 i → ‖y‖ ≤ RPar :=
    fun i y hy => gP.norm_radius i y (hB0sample i (tensorLocalInner_subset_sampling B0 i hy))
  obtain ⟨t⟩ := originalLocalBufferedCenters_construct RPar (bPar/4) hbPar' B0 hB0radius
  let AP := originalRefinedLocalFamily B0 RPar (bPar/4) hbPar' le_rfl t
  let KP := localRefinedSamplingCarrier RPar (bPar/4) hbPar' B0 t
  have hKP (i) : IsCompact (KP i) ∧ KP i ⊆ Q i :=
    ⟨localRefinedSamplingCarrier_compact RPar (bPar/4) hbPar' B0 t i,
      (localRefinedSamplingCarrier_sampling RPar (bPar/4) hbPar' B0 t le_rfl i).trans
        (hB0sample i)⟩
  have hSampleP : ∀ i, tensorLocalSamplingCoordinates AP i ⊆ KP i :=
    refinedLocalFamily_sampling_subset_carrier RPar (bPar/4) hbPar' B0 t le_rfl
  have hK : ∀ p ∈ K, ∃ i, p ∈ B0.inner i :=
    originalBufferedParameterFamily_cover chart (originalParameterSafeCoordinates chart Q W)
      bPar hbPar (fun i => inter_subset_left.trans (gP.norm_target i)) K gP.safe_ball_cover
  let rawP := localRefinedRawPreparation B0 W K RPar (bPar/4) hbPar' le_rfl t
    hChart hK (originalBufferedParameterSupportFamily_enlarged chart Q W bPar hbPar gP.norm_target)
    TP Dp hDp hPTrans
  refine ⟨s, rfl, rfl, rfl, refinedWorkingAtlas_smooth A0 Omega RSrc bSrc hbSrc
    le_rfl s hA0, sourceCompact_of_refined_carriers A0 Omega RSrc bSrc hbSrc le_rfl s
      hSample0 gS.norm_target, AP, KS, KP, rfl, ?_, hKS, hKP, hSampleS, hSampleP,
    rawS, rawP, rfl, rfl, ?_, ?_⟩
  · change (bPar/4)/8 = bPar/32
    ring
  · intro i
    apply compactSupport_of_internal_carrier (AS.chart i) (rawS.raw i) (KS i)
      (hKS i).1 ((hKS i).2.trans (gS.norm_target i))
    intro x hx
    have hi := rawS.inner_support i hx
    exact ⟨AS.inner_subset i hi, hSampleS i
      (bufferedInner_subset_sampling AS i (bufferedInnerCoordinates_mem AS i hi))⟩
  · intro i
    apply compactSupport_of_internal_carrier (AP.chart i) (rawP.raw i) (KP i)
      (hKP i).1 ((hKP i).2.trans (gP.norm_target i))
    intro p hp
    have hi := rawP.inner_support i hp
    exact ⟨AP.inner_subset i hi, hSampleP i
      (tensorLocalInner_subset_sampling AP i (tensorLocalInner_mem AP i hi))⟩

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.exists_uniform_originalCompactRawPair
