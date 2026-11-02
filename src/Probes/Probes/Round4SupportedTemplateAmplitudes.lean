import GlobalEmbedding.Offline.CompactGoodDictionaryTemplates
import GlobalEmbedding.Paper.IncrementsSupportedAmplitudeSmoothGlue

/-!
Literal supported square-root coefficients of the SAME good dictionary.
The actual tensor is reconstructed exactly from their squares. Smoothness
uses the existing original supported-amplitude theorem, so no positivity or
regularity of the tensor is required away from the cutoff support.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology TensorProduct BigOperators
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance supportedTemplateRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance supportedTemplateSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) := Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
private local instance supportedTemplateTensorNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
private local instance supportedTemplateTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def round4TemplateSupportedScalar (T : ActualGoodDictionaryTemplate E V)
    (chi : X → ℝ) (g : X → E →L[ℝ] E →L[ℝ] ℝ)
    (a : EdgePair (Module.finrank ℝ E + 1)) : X → ℝ :=
  fun x => chi x * Real.sqrt (T.coefficients (g x) a)

theorem round4_template_supported_scalar_smooth
    (T : ActualGoodDictionaryTemplate E V) (chi : X → ℝ)
    (g : X → E →L[ℝ] E →L[ℝ] ℝ) (O : Set X) (hO : IsOpen O)
    (hchi : ContDiff ℝ ∞ chi) (hg : ContDiffOn ℝ ∞ g O)
    (hsupport : tsupport chi ⊆ O)
    (hdom : ∀ x ∈ tsupport chi, g x ∈ T.tensorDomain)
    (a : EdgePair (Module.finrank ℝ E + 1)) :
    ContDiff ℝ ∞ (round4TemplateSupportedScalar T chi g a) ∧
      tsupport (round4TemplateSupportedScalar T chi g a) ⊆ tsupport chi := by
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a).comp T.coefficients
  have h := increments_supported_amplitude_contDiff O hO (fun _ => L) g chi (fun _ => (1 : ℝ))
    contDiffOn_const hg hchi.contDiffOn contDiffOn_const hsupport
    T.coefficientReserve T.coefficientReserve_pos
    (fun x hx => T.coefficient_control (g x) (hdom x hx) a)
  refine ⟨?_, tsupport_mul_subset_left⟩
  change ContDiff ℝ ∞ (fun x => chi x * Real.sqrt (T.coefficients (g x) a))
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, mul_one] using h

theorem round4_template_supported_scalar_reconstruct
    (T : ActualGoodDictionaryTemplate E V) (chi : X → ℝ)
    (g : X → E →L[ℝ] E →L[ℝ] ℝ) (x : X)
    (hdom : x ∈ tsupport chi → g x ∈ T.tensorDomain)
    (hsymm : x ∈ tsupport chi → ∀ v w, g x v w = g x w v) :
    continuousRankOneReconstruct T.covectors
      (fun a => round4TemplateSupportedScalar T chi g a x ^ 2) = chi x ^ 2 • g x := by
  by_cases hzero : chi x = 0
  · simp only [round4TemplateSupportedScalar, hzero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_smul]
    exact (continuousRankOneReconstruct T.covectors).map_zero
  · have hx : x ∈ tsupport chi := subset_tsupport _ (mem_support.mpr hzero)
    have heq : (fun a => round4TemplateSupportedScalar T chi g a x ^ 2) =
        chi x ^ 2 • (fun a => Real.sqrt (T.coefficients (g x) a) ^ 2) := by
      funext a
      simp only [round4TemplateSupportedScalar, mul_pow, Pi.smul_apply, smul_eq_mul]
    rw [heq, map_smul, T.amplitudes_reconstruct (g x) (hdom hx) (hsymm hx)]

theorem round4_template_square_family_reconstruct
    {ι : Type*} [Fintype ι] (T : ι → ActualGoodDictionaryTemplate E V)
    (chi : ι → X → ℝ) (g : X → E →L[ℝ] E →L[ℝ] ℝ) (x : X)
    (hpart : ∑ i, chi i x ^ 2 = 1)
    (hdom : ∀ i, x ∈ tsupport (chi i) → g x ∈ (T i).tensorDomain)
    (hsymm : ∀ i, x ∈ tsupport (chi i) → ∀ v w, g x v w = g x w v) :
    (∑ i, continuousRankOneReconstruct (T i).covectors
      (fun a => round4TemplateSupportedScalar (T i) (chi i) g a x ^ 2)) = g x := by
  simp_rw [round4_template_supported_scalar_reconstruct (T _) (chi _) g x (hdom _) (hsymm _)]
  rw [← Finset.sum_smul, hpart, one_smul]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_template_supported_scalar_smooth
#print axioms GlobalEmbedding.Continuation.round4_template_square_family_reconstruct
