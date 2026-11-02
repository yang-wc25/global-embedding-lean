import IncrementsCompletion.PositiveConjugationProfiles

/-!
# Positive-only composition and parameter conjugation at one slow scale

The same explicit positive-prefix costs apply to the true weighted jets
ell^(k-1).  The scale is chosen after those numerical profiles.  This
permits a primitive profile proved at the actual original input scale to
be used without replacing it by an unweighted or all-scale profile.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem incrementsCompletion_positive_trans_chart_weighted_at
    (FF GF : ℕ → ℝ)
    (hFF : ∀ k, 1 ≤ k → 0 ≤ FF k) (hGF : ∀ k, 1 ≤ k → 0 ≤ GF k)
    (f : OpenPartialHomeomorph X Y) (g : OpenPartialHomeomorph Y Z)
    (hf : ContDiffOn ℝ ∞ f f.source) (hg : ContDiffOn ℝ ∞ g g.source)
    (j : ℕ) (hj : 1 ≤ j) (x : X) (hx : x ∈ (f.trans g).source)
    (ell : ℝ) (hell : 0 < ell)
    (hfJ : ∀ k, 1 ≤ k → k ≤ j → ell^(k-1)*‖iteratedFDeriv ℝ k f x‖ ≤ FF k)
    (hgJ : ∀ k, 1 ≤ k → k ≤ j → ell^(k-1)*‖iteratedFDeriv ℝ k g (f x)‖ ≤ GF k) :
    ell^(j-1)*‖iteratedFDeriv ℝ j (f.trans g) x‖ ≤
      incrementsCompletionPositiveCompositionProfile GF FF j := by
  change ell^(j-1)*‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ _
  exact incrementsCompletion_positive_composition_at GF FF hGF hFF j hj f g
    (f.trans g).source g.source (f.trans g).open_source g.open_source
    (hf.mono (fun _ hy => hy.1)) hg (fun _ hy => hy.2) x hx ell hell hgJ hfJ

/-- The original parameter conjugation, using weighted native and parameter
jets at its three actual evaluation points and only at the present scale. -/
theorem incrementsCompletion_positive_parameter_conjugation_weighted_at
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
    (ell : ℝ) (hell : 0 < ell)
    (hbJ : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k b (B.symm z.1,z.2)‖ ≤ NF k)
    (hBJ : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (B.prod (OpenPartialHomeomorph.refl D))
        (b (B.symm z.1,z.2))‖ ≤ PF k)
    (hBiJ : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (B.prod (OpenPartialHomeomorph.refl D)).symm z‖ ≤ PI k) :
    ell^(j-1)*‖iteratedFDeriv ℝ j (round3ParameterChartPullback B b) z‖ ≤
      incrementsCompletionPositiveConjugationProfile NF PF PI j := by
  let C := B.prod (OpenPartialHomeomorph.refl D)
  have hInnerSmooth : ContDiffOn ℝ ∞ (C.symm.trans b) (C.symm.trans b).source :=
    hb.comp (hBi.mono (fun _ hw => hw.1)) (fun _ hw => hw.2)
  have hInner : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (C.symm.trans b) z‖ ≤
        incrementsCompletionPositiveCompositionProfile NF PI k := by
    intro k hk hkj
    exact incrementsCompletion_positive_trans_chart_weighted_at PI NF hPI hNF
      C.symm b hBi hb k hk z hz.1 ell hell
      (fun l hl hlk => hBiJ l hl (hlk.trans hkj))
      (fun l hl hlk => hbJ l hl (hlk.trans hkj))
  exact incrementsCompletion_positive_trans_chart_weighted_at
    (incrementsCompletionPositiveCompositionProfile NF PI) PF
    (fun k _ => incrementsCompletionPositiveCompositionProfile_nonneg NF PI hNF hPI k) hPF
    (C.symm.trans b) C hInnerSmooth hB j hj z hz ell hell hInner hBJ

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.incrementsCompletion_positive_trans_chart_weighted_at
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_positive_parameter_conjugation_weighted_at
