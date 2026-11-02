import GlobalEmbedding.Paper.ContractionCovectorFamily
import GlobalEmbedding.Paper.ContractionKernelDictionary
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The sole actual Good predicate is open in the full continuous covector space

Source: original `prop:saturation`, lines 948–953 and 971–995.
DAG: `linear-second-form-good-open`. Exclusive worker W2.
Only temporary coordinates of SAME ker B are used in the proof. The final set lives
on the FULL original continuous covectors. No source inner product or cone is assumed.
-/

noncomputable section
namespace GlobalEmbedding.Paper

/-- Nonzero scaling preserves the literal canonical Good predicate.
Source: conicality of the good covectors in the original saturation proof. -/
theorem linearSecondFormGoodCovector_smul_iff
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →ₗ[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) :
    LinearSecondFormGoodCovector B (c • ξ) ↔ LinearSecondFormGoodCovector B ξ := by
  unfold LinearSecondFormGoodCovector
  rw [LinearMap.ker_smul ξ c hc]
  simp only [ne_eq, smul_eq_zero, hc, false_or]

/-- Scaling invariance on the FULL continuous-covector space, with the same predicate.
Source: the actual good cone used in `prop:saturation`. -/
theorem linearSecondFormGoodCovector_continuous_smul_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) :
    LinearSecondFormGoodCovector B (c • ξ).toLinearMap ↔
      LinearSecondFormGoodCovector B ξ.toLinearMap :=
  linearSecondFormGoodCovector_smul_iff B ξ.toLinearMap c hc

/-- Actual Good is open on the FULL continuous covectors, without an inner product
on V or an externally supplied open cone. Source: original `prop:saturation`.

Proof: put the SAME ker B into finite basis coordinates only internally. The genuine
CLM-valued contraction family has an open injectivity locus by Mathlib. The native
coordinate equivalence preserves actual restricted injectivity. The already proved
same-B criterion identifies Good with this locus intersected with nonzero covectors.
The original phase-to-nonempty conversion is already `saturation_phaseRegular_iff_continuous_covector`.
-/
theorem isOpen_linearSecondFormGoodCovector
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) :
    IsOpen {ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap} := by
  let K := B.ker
  let C := Fin (Module.finrank ℝ K) → ℝ
  let e : K ≃ₗ[ℝ] C := (Module.finBasis ℝ K).equivFun
  let j : C →ₗ[ℝ] SymmetricSquare V := K.subtype.comp e.symm.toLinearMap
  let A : (V →L[ℝ] ℝ) →L[ℝ] (C →L[ℝ] V) := contractionKernelCovectorOperator j
  have hi (ξ : V →L[ℝ] ℝ) :
      Function.Injective ((contractionKernelQuotientMap ξ.toLinearMap).domRestrict K) ↔
        Function.Injective (A ξ) := by
    constructor
    · intro h u v huv
      have heq : e.symm u = e.symm v := h huv
      exact e.symm.injective heq
    · intro h u v huv
      apply e.injective
      apply h
      change contractionKernelQuotientMap ξ.toLinearMap
          (K.subtype (e.symm (e u))) =
        contractionKernelQuotientMap ξ.toLinearMap (K.subtype (e.symm (e v)))
      change contractionKernelQuotientMap ξ.toLinearMap (K.subtype u) =
        contractionKernelQuotientMap ξ.toLinearMap (K.subtype v) at huv
      simpa only [e.symm_apply_apply] using huv
  have heq : {ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap} =
      {ξ | ξ ≠ 0} ∩ {ξ | Function.Injective (A ξ)} := by
    ext ξ
    change LinearSecondFormGoodCovector B ξ.toLinearMap ↔
      ξ ≠ 0 ∧ Function.Injective (A ξ)
    rw [linearSecondFormGoodCovector_iff_contraction]
    have hn : ξ.toLinearMap ≠ 0 ↔ ξ ≠ 0 := by
      constructor
      · intro h hz
        apply h
        rw [hz]
        rfl
      · intro h hz
        apply h
        exact ContinuousLinearMap.coe_injective hz
    change (ξ.toLinearMap ≠ 0 ∧
      Function.Injective ((contractionKernelQuotientMap ξ.toLinearMap).domRestrict K)) ↔ _
    rw [hn, hi]
  have hn : IsOpen {ξ : V →L[ℝ] ℝ | ξ ≠ 0} := isClosed_singleton.isOpen_compl
  have ha : IsOpen {ξ : V →L[ℝ] ℝ | Function.Injective (A ξ)} :=
    ContinuousLinearMap.isOpen_injective.preimage A.continuous
  rw [heq]
  exact hn.inter ha

end GlobalEmbedding.Paper
