import Probes.Round4WeightedTemplateFamily

/-!
The same supported square-root amplitudes with actual hierarchical phases.
Inverse weights on amplitudes compensate the phase scaling exactly. Good
primary, doubled, and sum/difference phases are proved only where the actual
cutoffs overlap, using the selected templates there. A fixed numerical bound
on the refinement cardinal supplies bounded distinct labels within one host.
Combining different hosts still requires the original bounded host coloring.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology TensorProduct BigOperators
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance weightedFamilyRelationsClosed {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance weightedFamilySquareNormed {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) := Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {X E V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
private local instance weightedFamilyTensorNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private local instance weightedFamilyTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
variable {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
  {ι : Type} [Fintype ι]

def round4FiniteJetPrefix (B : ℕ → ℝ) (j : ℕ) : ℝ :=
  1+∑ k ∈ Finset.range (j+1), max 0 (B k)

theorem round4FiniteJetPrefix_nonneg (B : ℕ → ℝ) (j : ℕ) :
    0 ≤ round4FiniteJetPrefix B j :=
  add_nonneg zero_le_one (Finset.sum_nonneg (fun k _ => le_max_left _ _))

theorem round4_le_finite_jet_prefix (B : ℕ → ℝ) {k j : ℕ} (hk : k ≤ j) :
    B k ≤ round4FiniteJetPrefix B j := by
  apply (le_max_right 0 (B k)).trans
  have h := Finset.single_le_sum (fun q (_hq : q ∈ Finset.range (j+1)) => le_max_left 0 (B q))
    (by simpa using hk : k ∈ Finset.range (j+1))
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem round4_weighted_supported_template_jets
    (C : UniformActualGoodDictionaryCover K) (pick : ι → C.indices)
    (label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ)
    (chi : ι → X → ℝ) (g : X → E →L[ℝ] E →L[ℝ] ℝ)
    (O : Set X) (hO : IsOpen O) (hchi : ∀ z, ContDiff ℝ ∞ (chi z))
    (hg : ContDiffOn ℝ ∞ g O) (hsO : ∀ z, tsupport (chi z) ⊆ O)
    (hdom : ∀ z x, x ∈ tsupport (chi z) → g x ∈ (C.template (pick z)).tensorDomain)
    (Cut : ℕ → ℝ) (hCut : ∀ z k x, ‖iteratedFDeriv ℝ k (chi z) x‖ ≤ Cut k)
    (j : ℕ) (M : ℝ)
    (hM : ∀ z k, k ≤ j → ∀ x ∈ tsupport (chi z), ‖iteratedFDeriv ℝ k g x‖ ≤ M) :
    ∀ z a k, k ≤ j → ∀ x : X,
      ‖iteratedFDeriv ℝ k (round4WeightedTemplateScalar C pick label chi g z a) x‖ ≤
        round4SupportedTemplateJetConstant C j M (round4FiniteJetPrefix Cut j) := by
  intro z a k hk x
  have hs := round4_template_supported_scalar_smooth (C.template (pick z)) (chi z) g O hO
    (hchi z) hg (hsO z) (hdom z) a
  have hb := (round4_supported_template_scaled_jets C j M (round4FiniteJetPrefix Cut j)).2
    (pick z) a g (chi z) O hO (hsO z) hg (hchi z) 1 zero_lt_one (hdom z)
    (by simpa only [one_pow,one_mul] using hM z)
    (by
      intro q hq y _
      simpa only [one_pow,one_mul] using (hCut z q y).trans (round4_le_finite_jet_prefix Cut hq)) k hk x
  have hw := round4_hierarchical_amplitude_rescaling_jet C (label (z,a)) k
    (round4TemplateSupportedScalar (C.template (pick z)) (chi z) g a) hs.1 1 zero_le_one x
  change ‖iteratedFDeriv ℝ k (fun y =>
    round4TemplateSupportedScalar (C.template (pick z)) (chi z) g a y /
      (round4TemplateHierarchy C)^label (z,a)) x‖ ≤ _
  simpa only [one_pow,one_mul] using hw.trans hb


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_weighted_supported_template_jets
