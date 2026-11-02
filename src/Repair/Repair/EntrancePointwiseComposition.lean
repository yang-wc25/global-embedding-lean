import Repair.EntranceCompositionProfiles

/-!
# Composition jets on the actual original samples

Only the positive jets at the actual composition points are requested.
This permits atlas transition profiles on their literal sampling domains,
rather than requiring estimates on an enlarged or unbounded model.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

private theorem entrancePointPrefix_bound (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem repairEntrance_positive_trans_chart_at
    (FF GF : ℕ → ℝ) (hFF : ∀ j, 0 ≤ FF j) (hGF : ∀ j, 0 ≤ GF j)
    (f : OpenPartialHomeomorph X Y) (g : OpenPartialHomeomorph Y Z)
    (hf : ContDiffOn ℝ ∞ f f.source) (hg : ContDiffOn ℝ ∞ g g.source)
    (j : ℕ) (hj : 1 ≤ j) (x : X) (hx : x ∈ (f.trans g).source)
    (hfJ : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k f x‖ ≤ FF k)
    (hgJ : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k g (f x)‖ ≤ GF k) :
    ‖iteratedFDeriv ℝ j (f.trans g) x‖ ≤ repairEntranceCompositionProfile GF FF j := by
  have hb := actual_positive_joint_chart_composition FF hFF j hj f g
    (f.trans g).source g.source (f.trans g).open_source g.open_source
    (hf.mono (fun _ hy => hy.1)) hg (fun _ hy => hy.2) x hx
    1 (bufferedTransitionPrefix GF j) zero_lt_one
    (zero_le_one.trans (one_le_bufferedTransitionPrefix hGF j)) (by
      intro k hk hkj
      simp only [one_pow,one_mul]
      exact (hgJ k hk hkj).trans (entrancePointPrefix_bound GF hGF hkj)) (by
      intro k hk hkj
      simpa only [one_pow,one_mul] using hfJ k hk hkj)
  change ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ actualFastChartTransferCost FF j*bufferedTransitionPrefix GF j
  simpa only [one_pow,one_mul] using hb

/-- The literal nonlinear parameter conjugation at one original sample;
all three sets of primitive jets are evaluated at their true points. -/
theorem repairEntrance_positive_parameter_conjugation_at
    {Ep D : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (NF PF PI : ℕ → ℝ)
    (hNF : ∀ j, 0 ≤ NF j) (hPF : ∀ j, 0 ≤ PF j) (hPI : ∀ j, 0 ≤ PI j)
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
      repairEntranceConjugatedForwardProfile NF PF PI j := by
  let C := B.prod (OpenPartialHomeomorph.refl D)
  have hInnerSmooth : ContDiffOn ℝ ∞ (C.symm.trans b) (C.symm.trans b).source :=
    hb.comp (hBi.mono (fun _ hw => hw.1)) (fun _ hw => hw.2)
  have hInner : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (C.symm.trans b) z‖ ≤ repairEntranceCompositionProfile NF PI k := by
    intro k hk hkj
    exact repairEntrance_positive_trans_chart_at PI NF hPI hNF C.symm b hBi hb k hk z hz.1
      (fun l hl hlk => hBiJ l hl (hlk.trans hkj))
      (fun l hl hlk => hbJ l hl (hlk.trans hkj))
  exact repairEntrance_positive_trans_chart_at (repairEntranceCompositionProfile NF PI) PF
    (repairEntranceCompositionProfile_nonneg NF PI hNF hPI) hPF
    (C.symm.trans b) C hInnerSmooth hB j hj z hz hInner hBJ

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_positive_trans_chart_at
#print axioms GlobalEmbedding.Continuation.repairEntrance_positive_parameter_conjugation_at
