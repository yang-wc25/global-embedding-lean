import Probes.Round4TemplateCoefficientJets

/-!
All-source jets of the actual supported template amplitudes. Positivity and
tensor regularity are required only on an open containing the actual cutoff
support. Outside that support the literal amplitude is locally zero. The
same cutoff and coefficient operator are retained in the difference estimate.
The named constants depend only on the numerical cover and finite input jets.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance supportedJetsRelationsClosed {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance supportedJetsSquareNormed {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) := Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {E V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
private local instance supportedJetsTensorNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private local instance supportedJetsTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
variable {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}

def round4SupportedTemplateBudget (C : UniformActualGoodDictionaryCover K) (M Mcut : ℝ) : ℝ :=
  1+C.coefficientBound+max 0 M+max 0 Mcut

theorem round4SupportedTemplateBudget_nonneg (C : UniformActualGoodDictionaryCover K) (M Mcut : ℝ) :
    0 ≤ round4SupportedTemplateBudget C M Mcut := by
  dsimp [round4SupportedTemplateBudget]
  have := C.coefficientBound_pos
  positivity

def round4SupportedTemplateJetConstant (C : UniformActualGoodDictionaryCover K)
    (j : ℕ) (M Mcut : ℝ) : ℝ :=
  Classical.choose (increments_positive_reserve_amplitude_scaled_jets.{0,0,0}
    j C.coefficientReserve (round4SupportedTemplateBudget C M Mcut)
    C.coefficientReserve_pos (round4SupportedTemplateBudget_nonneg C M Mcut))

def round4SupportedTemplateDifferenceConstant (C : UniformActualGoodDictionaryCover K)
    (j : ℕ) (M Mcut : ℝ) : ℝ :=
  Classical.choose (increments_positive_reserve_amplitude_difference_scaled_jets.{0,0,0}
    j C.coefficientReserve (round4SupportedTemplateBudget C M Mcut)
    C.coefficientReserve_pos (round4SupportedTemplateBudget_nonneg C M Mcut))

private theorem supported_template_constant_jet
    {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (v : Y) (i : ℕ) (ell B : ℝ) (hB : 0 ≤ B) (hv : ‖v‖ ≤ B) (x : X) :
    ell^i*‖iteratedFDeriv ℝ i (fun _ : X => v) x‖ ≤ B := by
  by_cases hi : i = 0
  · subst i
    simpa using hv
  · rw [iteratedFDeriv_const_of_ne hi]
    simpa using hB

private theorem supported_template_zero_jet
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : ActualGoodDictionaryTemplate E V) (chi : X → ℝ)
    (g : X → E →L[ℝ] E →L[ℝ] ℝ)
    (a : EdgePair (Module.finrank ℝ E+1)) (x : X) (hx : x ∉ tsupport chi) (k : ℕ) :
    iteratedFDeriv ℝ k (round4TemplateSupportedScalar T chi g a) x = 0 := by
  let L := (ContinuousLinearMap.proj a).comp T.coefficients
  have heq : round4TemplateSupportedScalar T chi g a =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    change (fun y => chi y * Real.sqrt (T.coefficients (g y) a)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ))
    simpa only [smul_eq_mul, mul_one,
      L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      increments_supported_amplitude_eventually_zero (fun _ => L) g chi (fun _ => (1 : ℝ)) hx
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  simp

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem round4_supported_template_scaled_jets
    (C : UniformActualGoodDictionaryCover K) (j : ℕ) (M Mcut : ℝ) :
    0 ≤ round4SupportedTemplateJetConstant C j M Mcut ∧ ∀
      (i : C.indices) (a : EdgePair (Module.finrank ℝ E+1))
      (g : X → E →L[ℝ] E →L[ℝ] ℝ) (chi : X → ℝ) (O : Set X),
      IsOpen O → tsupport chi ⊆ O → ContDiffOn ℝ ∞ g O → ContDiff ℝ ∞ chi →
      ∀ (ell : ℝ), 0 < ell →
      (∀ x ∈ tsupport chi, g x ∈ (C.template i).tensorDomain) →
      (∀ k ≤ j, ∀ x ∈ tsupport chi, ell^k*‖iteratedFDeriv ℝ k g x‖ ≤ M) →
      (∀ k ≤ j, ∀ x ∈ tsupport chi, ell^k*‖iteratedFDeriv ℝ k chi x‖ ≤ Mcut) →
      ∀ k ≤ j, ∀ x : X,
        ell^k*‖iteratedFDeriv ℝ k (round4TemplateSupportedScalar (C.template i) chi g a) x‖ ≤
          round4SupportedTemplateJetConstant C j M Mcut := by
  have hspec := Classical.choose_spec (increments_positive_reserve_amplitude_scaled_jets.{0,0,0}
    j C.coefficientReserve (round4SupportedTemplateBudget C M Mcut)
    C.coefficientReserve_pos (round4SupportedTemplateBudget_nonneg C M Mcut))
  refine ⟨hspec.1, ?_⟩
  intro i a g chi O hO hsO hg hchi ell hell hdom hgj hchij k hk x
  by_cases hx : x ∈ tsupport chi
  · let B := round4SupportedTemplateBudget C M Mcut
    have hB : 0 ≤ B := round4SupportedTemplateBudget_nonneg C M Mcut
    have hcoeff : C.coefficientBound ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := le_max_left 0 M
      have := le_max_left 0 Mcut
      linarith
    have hM : M ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := C.coefficientBound_pos
      have := le_max_right 0 M
      have := le_max_left 0 Mcut
      linarith
    have hCut : Mcut ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := C.coefficientBound_pos
      have := le_max_right 0 Mcut
      have := le_max_left 0 M
      linarith
    have hone : (1 : ℝ) ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := C.coefficientBound_pos
      have := le_max_left 0 M
      have := le_max_left 0 Mcut
      linarith
    have hb := hspec.2 O (tsupport chi) hO hsO
      (fun _ => round4TemplateCoefficient C i a) g chi (fun _ => (1 : ℝ))
      contDiffOn_const hg hchi.contDiffOn contDiffOn_const ell hell
      (fun z hz => (C.bounds i).2.1.trans ((C.template i).coefficient_control (g z) (hdom z hz) a))
      (fun l hl z hz => supported_template_constant_jet _ l ell B hB
        ((round4TemplateCoefficient_norm C i a).trans hcoeff) z)
      (fun l hl z hz => (hgj l hl z hz).trans hM)
      (fun l hl z hz => (hchij l hl z hz).trans hCut)
      (fun l hl z hz => supported_template_constant_jet (1 : ℝ) l ell B hB (by simpa using hone) z)
      k hk x hx
    change ell^k*‖iteratedFDeriv ℝ k (fun y => chi y *
      Real.sqrt ((C.template i).coefficients (g y) a)) x‖ ≤ _
    simpa only [round4SupportedTemplateJetConstant, round4TemplateSupportedScalar, round4TemplateCoefficient,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_one] using hb
  · rw [supported_template_zero_jet (C.template i) chi g a x hx k, norm_zero, mul_zero]
    exact hspec.1

theorem round4_supported_template_difference_scaled_jets
    (C : UniformActualGoodDictionaryCover K) (j : ℕ) (M Mcut : ℝ) :
    0 ≤ round4SupportedTemplateDifferenceConstant C j M Mcut ∧ ∀
      (i : C.indices) (a : EdgePair (Module.finrank ℝ E+1))
      (g h : X → E →L[ℝ] E →L[ℝ] ℝ) (chi : X → ℝ) (O : Set X),
      IsOpen O → tsupport chi ⊆ O → ContDiffOn ℝ ∞ g O → ContDiffOn ℝ ∞ h O →
      ContDiff ℝ ∞ chi → ∀ (ell Delta : ℝ), 0 < ell → 0 ≤ Delta →
      (∀ x ∈ tsupport chi,
        g x ∈ (C.template i).tensorDomain ∧ h x ∈ (C.template i).tensorDomain) →
      (∀ k ≤ j, ∀ x ∈ tsupport chi, ell^k*‖iteratedFDeriv ℝ k g x‖ ≤ M) →
      (∀ k ≤ j, ∀ x ∈ tsupport chi, ell^k*‖iteratedFDeriv ℝ k h x‖ ≤ M) →
      (∀ k ≤ j, ∀ x ∈ tsupport chi, ell^k*‖iteratedFDeriv ℝ k chi x‖ ≤ Mcut) →
      (∀ k ≤ j, ∀ x ∈ tsupport chi,
        ell^k*‖iteratedFDeriv ℝ k (fun y => g y-h y) x‖ ≤ Delta) →
      ∀ k ≤ j, ∀ x : X,
        ell^k*‖iteratedFDeriv ℝ k (fun y =>
          round4TemplateSupportedScalar (C.template i) chi g a y -
          round4TemplateSupportedScalar (C.template i) chi h a y) x‖ ≤
            round4SupportedTemplateDifferenceConstant C j M Mcut*Delta := by
  have hspec := Classical.choose_spec (increments_positive_reserve_amplitude_difference_scaled_jets.{0,0,0}
    j C.coefficientReserve (round4SupportedTemplateBudget C M Mcut)
    C.coefficientReserve_pos (round4SupportedTemplateBudget_nonneg C M Mcut))
  refine ⟨hspec.1, ?_⟩
  intro i a g h chi O hO hsO hg hh hchi ell Delta hell hDelta hdom hgj hhj hchij hdiff k hk x
  by_cases hx : x ∈ tsupport chi
  · let B := round4SupportedTemplateBudget C M Mcut
    have hB : 0 ≤ B := round4SupportedTemplateBudget_nonneg C M Mcut
    have hcoeff : C.coefficientBound ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := le_max_left 0 M
      have := le_max_left 0 Mcut
      linarith
    have hM : M ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := C.coefficientBound_pos
      have := le_max_right 0 M
      have := le_max_left 0 Mcut
      linarith
    have hCut : Mcut ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := C.coefficientBound_pos
      have := le_max_right 0 Mcut
      have := le_max_left 0 M
      linarith
    have hone : (1 : ℝ) ≤ B := by
      dsimp [B, round4SupportedTemplateBudget]
      have := C.coefficientBound_pos
      have := le_max_left 0 M
      have := le_max_left 0 Mcut
      linarith
    have hb := hspec.2 O (tsupport chi) hO hsO
      (fun _ => round4TemplateCoefficient C i a) g h chi (fun _ => (1 : ℝ))
      contDiffOn_const hg hh hchi.contDiffOn contDiffOn_const ell Delta hell hDelta
      (fun z hz => ⟨(C.bounds i).2.1.trans ((C.template i).coefficient_control (g z) (hdom z hz).1 a),
        (C.bounds i).2.1.trans ((C.template i).coefficient_control (h z) (hdom z hz).2 a)⟩)
      (fun l hl z hz => supported_template_constant_jet _ l ell B hB
        ((round4TemplateCoefficient_norm C i a).trans hcoeff) z)
      (fun l hl z hz => (hgj l hl z hz).trans hM)
      (fun l hl z hz => (hhj l hl z hz).trans hM)
      (fun l hl z hz => (hchij l hl z hz).trans hCut)
      (fun l hl z hz => supported_template_constant_jet (1 : ℝ) l ell B hB (by simpa using hone) z)
      hdiff k hk x hx
    change ell^k*‖iteratedFDeriv ℝ k (fun y =>
      chi y*Real.sqrt ((C.template i).coefficients (g y) a)-
      chi y*Real.sqrt ((C.template i).coefficients (h y) a)) x‖ ≤ _
    simpa only [round4SupportedTemplateDifferenceConstant, round4TemplateCoefficient,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_one] using hb
  · have heq : (fun y =>
        round4TemplateSupportedScalar (C.template i) chi g a y -
        round4TemplateSupportedScalar (C.template i) chi h a y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport chi).isOpen_compl.mem_nhds hx] with y hy
      simp only [round4TemplateSupportedScalar, image_eq_zero_of_notMem_tsupport hy, zero_mul, sub_self]
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    simpa [round4SupportedTemplateDifferenceConstant] using mul_nonneg hspec.1 hDelta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_supported_template_scaled_jets
#print axioms GlobalEmbedding.Continuation.round4_supported_template_difference_scaled_jets
