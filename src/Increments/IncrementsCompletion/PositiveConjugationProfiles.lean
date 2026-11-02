import IncrementsCompletion.PositiveCompositionProfiles

/-!
# The literal parameter conjugation with positive-only numerical reads

All three primitive jet lists are evaluated at the actual points of the
same nonlinear parameter conjugation.  The explicit cost depends only on
their positive prefixes; neither NF(0), PF(0), PI(0), nor any coordinate
value is read.  No native chart or original sample is changed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def incrementsCompletionPositiveConjugationProfile (NF PF PI : ℕ → ℝ) : ℕ → ℝ :=
  incrementsCompletionPositiveCompositionProfile PF
    (incrementsCompletionPositiveCompositionProfile NF PI)

theorem incrementsCompletionPositiveConjugationProfile_nonneg
    (NF PF PI : ℕ → ℝ)
    (hNF : ∀ k, 1 ≤ k → 0 ≤ NF k) (hPF : ∀ k, 1 ≤ k → 0 ≤ PF k)
    (hPI : ∀ k, 1 ≤ k → 0 ≤ PI k) (j : ℕ) :
    0 ≤ incrementsCompletionPositiveConjugationProfile NF PF PI j :=
  incrementsCompletionPositiveCompositionProfile_nonneg _ _ hPF
    (fun k _ => incrementsCompletionPositiveCompositionProfile_nonneg NF PI hNF hPI k) j

/-- The original zero entries and all tails above j are irrelevant. -/
theorem incrementsCompletionPositiveConjugationProfile_prefix_congr
    (NF PF PI NF' PF' PI' : ℕ → ℝ) (j : ℕ)
    (hNF : ∀ k, 1 ≤ k → k ≤ j → NF k = NF' k)
    (hPF : ∀ k, 1 ≤ k → k ≤ j → PF k = PF' k)
    (hPI : ∀ k, 1 ≤ k → k ≤ j → PI k = PI' k) :
    incrementsCompletionPositiveConjugationProfile NF PF PI j =
      incrementsCompletionPositiveConjugationProfile NF' PF' PI' j := by
  apply incrementsCompletionPositiveCompositionProfile_prefix_congr _ _ _ _ j hPF
  intro k hk hkj
  apply incrementsCompletionPositiveCompositionProfile_prefix_congr _ _ _ _ k
  · intro l hl hlk
    exact hNF l hl (hlk.trans hkj)
  · intro l hl hlk
    exact hPI l hl (hlk.trans hkj)

/-- The actual conjugation at the actual original sample, with no value
bound and no zeroth-order budget dependency. -/
theorem incrementsCompletion_positive_parameter_conjugation_at
    {Ep D : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (NF PF PI : ℕ → ℝ)
    (hNF : ∀ k, 1 ≤ k → 0 ≤ NF k) (hPF : ∀ k, 1 ≤ k → 0 ≤ PF k)
    (hPI : ∀ k, 1 ≤ k → 0 ≤ PI k)
    (B : OpenPartialHomeomorph Ep Ep) (b : OpenPartialHomeomorph (Ep × D) (Ep × D))
    (hb : ContDiffOn ℝ ∞ b b.source)
    (hB : ContDiffOn ℝ ∞ (B.prod (OpenPartialHomeomorph.refl D))
      (B.prod (OpenPartialHomeomorph.refl D)).source)
    (hBi : ContDiffOn ℝ ∞ (B.prod (OpenPartialHomeomorph.refl D)).symm
      (B.prod (OpenPartialHomeomorph.refl D)).target)
    (j : ℕ) (hj : 1 ≤ j) (z : Ep × D) (hz : z ∈ (round3ParameterChartPullback B b).source)
    (hbJ : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k b (B.symm z.1,z.2)‖ ≤ NF k)
    (hBJ : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (B.prod (OpenPartialHomeomorph.refl D)) (b (B.symm z.1,z.2))‖ ≤ PF k)
    (hBiJ : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (B.prod (OpenPartialHomeomorph.refl D)).symm z‖ ≤ PI k) :
    ‖iteratedFDeriv ℝ j (round3ParameterChartPullback B b) z‖ ≤
      incrementsCompletionPositiveConjugationProfile NF PF PI j := by
  let C := B.prod (OpenPartialHomeomorph.refl D)
  have hInnerSmooth : ContDiffOn ℝ ∞ (C.symm.trans b) (C.symm.trans b).source :=
    hb.comp (hBi.mono (fun _ hw => hw.1)) (fun _ hw => hw.2)
  have hInner : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (C.symm.trans b) z‖ ≤
        incrementsCompletionPositiveCompositionProfile NF PI k := by
    intro k hk hkj
    exact incrementsCompletion_positive_trans_chart_at PI NF hPI hNF C.symm b hBi hb k hk z hz.1
      (fun l hl hlk => hBiJ l hl (hlk.trans hkj))
      (fun l hl hlk => hbJ l hl (hlk.trans hkj))
  exact incrementsCompletion_positive_trans_chart_at
    (incrementsCompletionPositiveCompositionProfile NF PI) PF
    (fun k _ => incrementsCompletionPositiveCompositionProfile_nonneg NF PI hNF hPI k) hPF
    (C.symm.trans b) C hInnerSmooth hB j hj z hz hInner hBJ

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsCompletionPositiveConjugationProfile_prefix_congr
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_positive_parameter_conjugation_at
