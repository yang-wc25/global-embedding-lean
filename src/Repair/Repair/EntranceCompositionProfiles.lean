import Repair.EntranceRehostedProfiles
import Probes.Round3ParameterCrossHostConjugation
import Probes.ActualPositiveChartComposition

/-!
# Numerical composition profiles for the actual original observers

The constants are fixed before the charts and retain order zero as well
as every joint parameter derivative.  They apply to the literal partial
homeomorphism compositions, including their true source and target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

private theorem entranceCompositionPrefix_bound (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {k j : ℕ} (hkj : k ≤ j) : P k ≤ bufferedTransitionPrefix P j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hP l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem repairEntrance_trans_chart_profiles
    (FF FI GF GI : ℕ → ℝ)
    (hFF : ∀ j, 0 ≤ FF j) (hFI : ∀ j, 0 ≤ FI j)
    (hGF : ∀ j, 0 ≤ GF j) (hGI : ∀ j, 0 ≤ GI j)
    (f : OpenPartialHomeomorph X Y) (g : OpenPartialHomeomorph Y Z)
    (hf : ContDiffOn ℝ ∞ f f.source) (hfi : ContDiffOn ℝ ∞ f.symm f.target)
    (hg : ContDiffOn ℝ ∞ g g.source) (hgi : ContDiffOn ℝ ∞ g.symm g.target)
    (hfJ : ∀ j x, x ∈ f.source → ‖iteratedFDeriv ℝ j f x‖ ≤ FF j)
    (hfiJ : ∀ j x, x ∈ f.target → ‖iteratedFDeriv ℝ j f.symm x‖ ≤ FI j)
    (hgJ : ∀ j x, x ∈ g.source → ‖iteratedFDeriv ℝ j g x‖ ≤ GF j)
    (hgiJ : ∀ j x, x ∈ g.target → ‖iteratedFDeriv ℝ j g.symm x‖ ≤ GI j) :
    (∀ j x, x ∈ (f.trans g).source → ‖iteratedFDeriv ℝ j (f.trans g) x‖ ≤
      repairEntranceCompositionProfile GF FF j) ∧
    ∀ j x, x ∈ (f.trans g).target → ‖iteratedFDeriv ℝ j (f.trans g).symm x‖ ≤
      repairEntranceCompositionProfile FI GI j := by
  constructor
  · intro j x hx
    have hb := actual_fast_joint_chart_transfer FF hFF j f g
      (f.trans g).source g.source (f.trans g).open_source g.open_source
      (hf.mono (fun _ hy => hy.1)) hg (fun _ hy => hy.2) x hx
      1 1 (bufferedTransitionPrefix GF j) zero_lt_one le_rfl (by
        intro k hk
        simp only [one_pow,one_mul]
        exact (hgJ k (f x) hx.2).trans (entranceCompositionPrefix_bound GF hGF hk)) (by
        intro k hk hkj
        simpa only [one_pow,one_mul] using hfJ k x hx.1)
    change ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ actualFastChartTransferCost FF j*bufferedTransitionPrefix GF j
    simpa only [one_pow,one_mul] using hb
  · intro j x hx
    have hb := actual_fast_joint_chart_transfer GI hGI j g.symm f.symm
      (f.trans g).target f.target (f.trans g).open_target f.open_target
      (hgi.mono (fun _ hy => hy.1)) hfi (fun _ hy => hy.2) x hx
      1 1 (bufferedTransitionPrefix FI j) zero_lt_one le_rfl (by
        intro k hk
        simp only [one_pow,one_mul]
        exact (hfiJ k (g.symm x) hx.2).trans (entranceCompositionPrefix_bound FI hFI hk)) (by
        intro k hk hkj
        simpa only [one_pow,one_mul] using hgiJ k x hx.1)
    change ‖iteratedFDeriv ℝ j (f.symm ∘ g.symm) x‖ ≤ actualFastChartTransferCost GI j*bufferedTransitionPrefix FI j
    simpa only [one_pow,one_mul] using hb

/-- Positive composition needs no global bound on a coordinate value. This
is essential for products of parameter transitions with the spatial identity. -/
theorem repairEntrance_positive_trans_chart_profiles
    (FF FI GF GI : ℕ → ℝ)
    (hFF : ∀ j, 0 ≤ FF j) (hFI : ∀ j, 0 ≤ FI j)
    (hGF : ∀ j, 0 ≤ GF j) (hGI : ∀ j, 0 ≤ GI j)
    (f : OpenPartialHomeomorph X Y) (g : OpenPartialHomeomorph Y Z)
    (hf : ContDiffOn ℝ ∞ f f.source) (hfi : ContDiffOn ℝ ∞ f.symm f.target)
    (hg : ContDiffOn ℝ ∞ g g.source) (hgi : ContDiffOn ℝ ∞ g.symm g.target)
    (hfJ : ∀ j, 1 ≤ j → ∀ x ∈ f.source, ‖iteratedFDeriv ℝ j f x‖ ≤ FF j)
    (hfiJ : ∀ j, 1 ≤ j → ∀ x ∈ f.target, ‖iteratedFDeriv ℝ j f.symm x‖ ≤ FI j)
    (hgJ : ∀ j, 1 ≤ j → ∀ x ∈ g.source, ‖iteratedFDeriv ℝ j g x‖ ≤ GF j)
    (hgiJ : ∀ j, 1 ≤ j → ∀ x ∈ g.target, ‖iteratedFDeriv ℝ j g.symm x‖ ≤ GI j) :
    (∀ j, 1 ≤ j → ∀ x ∈ (f.trans g).source, ‖iteratedFDeriv ℝ j (f.trans g) x‖ ≤
      repairEntranceCompositionProfile GF FF j) ∧
    ∀ j, 1 ≤ j → ∀ x ∈ (f.trans g).target, ‖iteratedFDeriv ℝ j (f.trans g).symm x‖ ≤
      repairEntranceCompositionProfile FI GI j := by
  constructor
  · intro j hj x hx
    have hb := actual_positive_joint_chart_composition FF hFF j hj f g
      (f.trans g).source g.source (f.trans g).open_source g.open_source
      (hf.mono (fun _ hy => hy.1)) hg (fun _ hy => hy.2) x hx
      1 (bufferedTransitionPrefix GF j) zero_lt_one
      (zero_le_one.trans (one_le_bufferedTransitionPrefix hGF j)) (by
        intro k hk hkj
        simp only [one_pow,one_mul]
        exact (hgJ k hk (f x) hx.2).trans (entranceCompositionPrefix_bound GF hGF hkj)) (by
        intro k hk hkj
        simpa only [one_pow,one_mul] using hfJ k hk x hx.1)
    change ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ actualFastChartTransferCost FF j*bufferedTransitionPrefix GF j
    simpa only [one_pow,one_mul] using hb
  · intro j hj x hx
    have hb := actual_positive_joint_chart_composition GI hGI j hj g.symm f.symm
      (f.trans g).target f.target (f.trans g).open_target f.open_target
      (hgi.mono (fun _ hy => hy.1)) hfi (fun _ hy => hy.2) x hx
      1 (bufferedTransitionPrefix FI j) zero_lt_one
      (zero_le_one.trans (one_le_bufferedTransitionPrefix hFI j)) (by
        intro k hk hkj
        simp only [one_pow,one_mul]
        exact (hfiJ k hk (g.symm x) hx.2).trans (entranceCompositionPrefix_bound FI hFI hkj)) (by
        intro k hk hkj
        simpa only [one_pow,one_mul] using hgiJ k hk x hx.1)
    change ‖iteratedFDeriv ℝ j (f.symm ∘ g.symm) x‖ ≤ actualFastChartTransferCost GI j*bufferedTransitionPrefix FI j
    simpa only [one_pow,one_mul] using hb

def repairEntranceConjugatedForwardProfile (NativeForward ParameterForward ParameterInverse : ℕ → ℝ) :=
  repairEntranceCompositionProfile ParameterForward
    (repairEntranceCompositionProfile NativeForward ParameterInverse)

def repairEntranceConjugatedInverseProfile (NativeInverse ParameterForward ParameterInverse : ℕ → ℝ) :=
  repairEntranceCompositionProfile
    (repairEntranceCompositionProfile ParameterForward NativeInverse) ParameterInverse

/-- Nonlinear parameter changes are retained on both sides of the very
same native phase chart. Every native joint derivative is accounted for. -/
theorem repairEntrance_parameter_conjugated_positive_profiles
    {Ep D : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (NF NI PF PI : ℕ → ℝ)
    (hNF : ∀ j, 0 ≤ NF j) (hNI : ∀ j, 0 ≤ NI j)
    (hPF : ∀ j, 0 ≤ PF j) (hPI : ∀ j, 0 ≤ PI j)
    (B : OpenPartialHomeomorph Ep Ep) (b : OpenPartialHomeomorph (Ep × D) (Ep × D))
    (hb : ContDiffOn ℝ ∞ b b.source) (hbi : ContDiffOn ℝ ∞ b.symm b.target)
    (hB : ContDiffOn ℝ ∞ (B.prod (OpenPartialHomeomorph.refl D))
      (B.prod (OpenPartialHomeomorph.refl D)).source)
    (hBi : ContDiffOn ℝ ∞ (B.prod (OpenPartialHomeomorph.refl D)).symm
      (B.prod (OpenPartialHomeomorph.refl D)).target)
    (hbJ : ∀ j, 1 ≤ j → ∀ z, z ∈ b.source → ‖iteratedFDeriv ℝ j b z‖ ≤ NF j)
    (hbiJ : ∀ j, 1 ≤ j → ∀ z, z ∈ b.target → ‖iteratedFDeriv ℝ j b.symm z‖ ≤ NI j)
    (hBJ : ∀ j, 1 ≤ j → ∀ z, z ∈ (B.prod (OpenPartialHomeomorph.refl D)).source →
      ‖iteratedFDeriv ℝ j (B.prod (OpenPartialHomeomorph.refl D)) z‖ ≤ PF j)
    (hBiJ : ∀ j, 1 ≤ j → ∀ z, z ∈ (B.prod (OpenPartialHomeomorph.refl D)).target →
      ‖iteratedFDeriv ℝ j (B.prod (OpenPartialHomeomorph.refl D)).symm z‖ ≤ PI j) :
    (∀ j, 1 ≤ j → ∀ z, z ∈ (round3ParameterChartPullback B b).source →
      ‖iteratedFDeriv ℝ j (round3ParameterChartPullback B b) z‖ ≤
        repairEntranceConjugatedForwardProfile NF PF PI j) ∧
    ∀ j, 1 ≤ j → ∀ z, z ∈ (round3ParameterChartPullback B b).target →
      ‖iteratedFDeriv ℝ j (round3ParameterChartPullback B b).symm z‖ ≤
        repairEntranceConjugatedInverseProfile NI PF PI j := by
  let C := B.prod (OpenPartialHomeomorph.refl D)
  have hInner := repairEntrance_positive_trans_chart_profiles PI PF NF NI hPI hPF hNF hNI
    C.symm b hBi hB hb hbi hBiJ hBJ hbJ hbiJ
  have hInnerSmooth : ContDiffOn ℝ ∞ (C.symm.trans b) (C.symm.trans b).source :=
    hb.comp (hBi.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hInnerInvSmooth : ContDiffOn ℝ ∞ (C.symm.trans b).symm (C.symm.trans b).target :=
    hB.comp (hbi.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  exact repairEntrance_positive_trans_chart_profiles
    (repairEntranceCompositionProfile NF PI) (repairEntranceCompositionProfile PF NI) PF PI
    (repairEntranceCompositionProfile_nonneg NF PI hNF hPI)
    (repairEntranceCompositionProfile_nonneg PF NI hPF hNI) hPF hPI
    (C.symm.trans b) C hInnerSmooth hInnerInvSmooth hB hBi hInner.1 hInner.2 hBJ hBiJ

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_trans_chart_profiles
#print axioms GlobalEmbedding.Continuation.repairEntrance_positive_trans_chart_profiles
#print axioms GlobalEmbedding.Continuation.repairEntrance_parameter_conjugated_positive_profiles
