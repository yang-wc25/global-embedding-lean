import Probes.Round4SupportedTemplateJets
import Probes.Round4UniformTemplateSquareFamily

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

def round4TemplateHierarchy (C : UniformActualGoodDictionaryCover K) : ℝ :=
  hierarchicalGoodWeight C.covectorRadius C.covectorBound

theorem round4TemplateHierarchy_gt_one (C : UniformActualGoodDictionaryCover K) :
    1 < round4TemplateHierarchy C :=
  hierarchicalGoodWeight_gt_one C.covectorRadius_pos C.covectorBound_pos.le

def round4WeightedTemplateCovector (C : UniformActualGoodDictionaryCover K)
    (pick : ι → C.indices) (label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ)
    (z : ι) (a : EdgePair (Module.finrank ℝ E+1)) : E →L[ℝ] ℝ :=
  (round4TemplateHierarchy C)^label (z,a) • (C.template (pick z)).covectors a

def round4WeightedTemplateScalar (C : UniformActualGoodDictionaryCover K)
    (pick : ι → C.indices) (label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ)
    (chi : ι → X → ℝ) (g : X → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ι) (a : EdgePair (Module.finrank ℝ E+1)) : X → ℝ :=
  fun x => round4TemplateSupportedScalar (C.template (pick z)) (chi z) g a x /
    (round4TemplateHierarchy C)^label (z,a)

theorem round4_weighted_template_reconstruct
    (C : UniformActualGoodDictionaryCover K) (pick : ι → C.indices)
    (label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ)
    (chi : ι → X → ℝ) (g : X → E →L[ℝ] E →L[ℝ] ℝ) (x : X)
    (hpart : ∑ z, chi z x ^ 2 = 1)
    (hdom : ∀ z, x ∈ tsupport (chi z) → g x ∈ (C.template (pick z)).tensorDomain)
    (hsymm : ∀ z, x ∈ tsupport (chi z) → ∀ v w, g x v w = g x w v) :
    (∑ z, continuousRankOneReconstruct (round4WeightedTemplateCovector C pick label z)
      (fun a => round4WeightedTemplateScalar C pick label chi g z a x ^ 2)) = g x := by
  have hnonzero : round4TemplateHierarchy C ≠ 0 :=
    (zero_lt_one.trans (round4TemplateHierarchy_gt_one C)).ne'
  calc
    _ = ∑ z, continuousRankOneReconstruct (C.template (pick z)).covectors
        (fun a => round4TemplateSupportedScalar (C.template (pick z)) (chi z) g a x ^ 2) := by
      apply Finset.sum_congr rfl
      intro z _
      change continuousRankOneReconstruct
        (fun a => (round4TemplateHierarchy C)^label (z,a) • (C.template (pick z)).covectors a)
        (fun a => (round4TemplateSupportedScalar (C.template (pick z)) (chi z) g a x /
          (round4TemplateHierarchy C)^label (z,a))^2) = _
      simpa only [round4WeightedTemplateCovector, round4WeightedTemplateScalar, div_pow] using
        rank_one_inverse_square_rescaling (C.template (pick z)).covectors
          (fun a => (round4TemplateHierarchy C)^label (z,a))
          (fun a => round4TemplateSupportedScalar (C.template (pick z)) (chi z) g a x ^ 2)
          (fun a => pow_ne_zero _ hnonzero)
    _ = g x := round4_template_square_family_reconstruct (fun z => C.template (pick z))
      chi g x hpart hdom hsymm

theorem round4_weighted_template_smooth
    (C : UniformActualGoodDictionaryCover K) (pick : ι → C.indices)
    (label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ)
    (chi : ι → X → ℝ) (g : X → E →L[ℝ] E →L[ℝ] ℝ)
    (O : Set X) (hO : IsOpen O) (hchi : ∀ z, ContDiff ℝ ∞ (chi z))
    (hg : ContDiffOn ℝ ∞ g O) (hsO : ∀ z, tsupport (chi z) ⊆ O)
    (hdom : ∀ z x, x ∈ tsupport (chi z) → g x ∈ (C.template (pick z)).tensorDomain) :
    ∀ z a, ContDiff ℝ ∞ (round4WeightedTemplateScalar C pick label chi g z a) ∧
      tsupport (round4WeightedTemplateScalar C pick label chi g z a) ⊆ tsupport (chi z) := by
  intro z a
  have h := round4_template_supported_scalar_smooth (C.template (pick z)) (chi z) g O hO
    (hchi z) hg (hsO z) (hdom z) a
  refine ⟨h.1.div_const _, ?_⟩
  change tsupport (fun x => round4TemplateSupportedScalar (C.template (pick z)) (chi z) g a x /
    (round4TemplateHierarchy C)^label (z,a)) ⊆ _
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left.trans h.2

theorem round4_weighted_template_interactions_on_support
    (C : UniformActualGoodDictionaryCover K) (pick : ι → C.indices)
    (label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ)
    (chi : ι → X → ℝ) (B : X → SymmetricSquare E →L[ℝ] V)
    (hdom : ∀ z x, x ∈ tsupport (chi z) → B x ∈ (C.template (pick z)).operatorDomain)
    (hlabel : ∀ x (za zb : ι × EdgePair (Module.finrank ℝ E+1)),
      x ∈ tsupport (chi za.1) → x ∈ tsupport (chi zb.1) → za ≠ zb → label za ≠ label zb) :
    (∀ z a x, x ∈ tsupport (chi z) →
      LinearSecondFormGoodCovector (B x).toLinearMap
        (round4WeightedTemplateCovector C pick label z a).toLinearMap) ∧
    (∀ z a x, x ∈ tsupport (chi z) →
      LinearSecondFormGoodCovector (B x).toLinearMap
        ((2 : ℝ) • round4WeightedTemplateCovector C pick label z a).toLinearMap) ∧
    (∀ x (za zb : ι × EdgePair (Module.finrank ℝ E+1)),
      x ∈ tsupport (chi za.1) → x ∈ tsupport (chi zb.1) → za ≠ zb →
      LinearSecondFormGoodCovector (B x).toLinearMap
        (round4WeightedTemplateCovector C pick label za.1 za.2 +
          round4WeightedTemplateCovector C pick label zb.1 zb.2).toLinearMap ∧
      LinearSecondFormGoodCovector (B x).toLinearMap
        (round4WeightedTemplateCovector C pick label za.1 za.2 -
          round4WeightedTemplateCovector C pick label zb.1 zb.2).toLinearMap) := by
  have hactive (x : X) := C.labeled_interactions_good (B x)
    (fun q : {q : ι × EdgePair (Module.finrank ℝ E+1) // x ∈ tsupport (chi q.1)} => pick q.val.1)
    (fun q => q.val.2) (fun q => label q.val) (fun q => hdom q.val.1 x q.property)
  refine ⟨?_, ?_, ?_⟩
  · intro z a x hx
    exact (hactive x).1 ⟨(z,a),hx⟩
  · intro z a x hx
    exact (hactive x).2.1 ⟨(z,a),hx⟩
  · intro x za zb hza hzb hne
    exact (hactive x).2.2 ⟨za,hza⟩ ⟨zb,hzb⟩ (hlabel x za zb hza hzb hne)

theorem round4_bounded_host_template_labels
    (pieceBound : ℕ) (hcard : Fintype.card ι ≤ pieceBound) :
    ∃ label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ,
      Function.Injective label ∧ ∀ q,
        label q < pieceBound * Fintype.card (EdgePair (Module.finrank ℝ E+1)) := by
  classical
  let e := Fintype.equivFin (ι × EdgePair (Module.finrank ℝ E+1))
  refine ⟨fun q => (e q).val, ?_, ?_⟩
  · intro p q hpq
    exact e.injective (Fin.ext hpq)
  · intro q
    apply (e q).isLt.trans_le
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul_right _ hcard

theorem round4_weighted_template_covector_bound
    (C : UniformActualGoodDictionaryCover K) (pick : ι → C.indices)
    (label : ι × EdgePair (Module.finrank ℝ E+1) → ℕ)
    (L : ℕ) (hlabel : ∀ q, label q ≤ L) (z : ι) (a : EdgePair (Module.finrank ℝ E+1)) :
    ‖round4WeightedTemplateCovector C pick label z a‖ ≤
      (round4TemplateHierarchy C)^L*C.covectorBound := by
  have hLambda := round4TemplateHierarchy_gt_one C
  change ‖(round4TemplateHierarchy C)^label (z,a) • (C.template (pick z)).covectors a‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (zero_lt_one.trans hLambda).le _)]
  exact mul_le_mul (pow_le_pow_right₀ hLambda.le (hlabel (z,a)))
    ((C.bounds (pick z)).2.2.2.2 a) (norm_nonneg _) (pow_nonneg (zero_lt_one.trans hLambda).le _)

/-- The inverse phase weight does not enlarge any actual joint jet. This
applies to the actual supported amplitude and, unchanged, to its input difference. -/
theorem round4_hierarchical_amplitude_rescaling_jet
    (C : UniformActualGoodDictionaryCover K) (label k : ℕ)
    (f : X → ℝ) (hf : ContDiff ℝ ∞ f) (ell : ℝ) (hell : 0 ≤ ell) (x : X) :
    ell^k*‖iteratedFDeriv ℝ k (fun y => f y/(round4TemplateHierarchy C)^label) x‖ ≤
      ell^k*‖iteratedFDeriv ℝ k f x‖ := by
  have hLambda := round4TemplateHierarchy_gt_one C
  have hpow : 1 ≤ (round4TemplateHierarchy C)^label := one_le_pow₀ hLambda.le
  have hinv : 0 ≤ ((round4TemplateHierarchy C)^label)⁻¹ := inv_nonneg.mpr (by positivity)
  have hinv1 : ((round4TemplateHierarchy C)^label)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow
  have heq : (fun y => f y/(round4TemplateHierarchy C)^label) =
      (fun y => ((round4TemplateHierarchy C)^label)⁻¹ • f y) := by
    funext y
    simp only [div_eq_mul_inv, smul_eq_mul, mul_comm]
  rw [heq, iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by simp)),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  calc
    _ = ((round4TemplateHierarchy C)^label)⁻¹ * (ell^k*‖iteratedFDeriv ℝ k f x‖) := by ring
    _ ≤ 1 * (ell^k*‖iteratedFDeriv ℝ k f x‖) :=
      mul_le_mul_of_nonneg_right hinv1 (mul_nonneg (pow_nonneg hell _) (norm_nonneg _))
    _ = _ := one_mul _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_weighted_template_reconstruct
#print axioms GlobalEmbedding.Continuation.round4_weighted_template_interactions_on_support
#print axioms GlobalEmbedding.Continuation.round4_bounded_host_template_labels
#print axioms GlobalEmbedding.Continuation.round4_hierarchical_amplitude_rescaling_jet
