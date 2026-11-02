import GlobalEmbedding.Paper.QuotientContraction
import GlobalEmbedding.Paper.ContractionKernelSymmetricSquareInclusion
import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation
import GlobalEmbedding.Paper.SupportedRankSymmetricSquareSplitting
import GlobalEmbedding.Paper.SupportedLocusLocalEquations
import Mathlib.Tactic.Linarith

/-!
# The literal contraction kernel and the original symmetric-square inclusion

Source: original `prop:saturation`, lines 948–983. Existing DAG nodes
`good-kernel-contraction` and `contraction-kernel-image-annihilated`.
Exclusive worker W2. The accepted general splitting is reused, not reconstructed.
-/

noncomputable section
open scoped TensorProduct

namespace GlobalEmbedding.Paper

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem dictionaryMap_product {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E →ₗ[ℝ] F) (v w : E) :
    symmetricSquareLinearMap f (symmetricSquareProduct E v w) =
      symmetricSquareProduct F (f v) (f w) := by
  exact symmetricBilinearDescend_product
    (((symmetricSquareProduct F).compl₂ f).comp f)
    (fun v w ↦ symmetricSquareProduct_comm F (f v) (f w)) v w

/-- The old tensor-quotient inclusion is the actual functor used by GoodCovector.
Source: literal `Sym² ker ξ` restriction in `defn:phase` and `prop:saturation`. -/
theorem contractionKernel_inclusion_eq_linearMap (ξ : V →ₗ[ℝ] ℝ) :
    contractionKernelSymmetricSquareInclusion ξ =
      symmetricSquareLinearMap ξ.ker.subtype := by
  apply (symmetricSquareRelations ξ.ker).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change contractionKernelSymmetricSquareInclusion ξ (symmetricSquareProduct ξ.ker v w) =
    symmetricSquareLinearMap ξ.ker.subtype (symmetricSquareProduct ξ.ker v w)
  rw [dictionaryMap_product]
  change contractionKernelSymmetricSquareInclusion ξ
    (Submodule.Quotient.mk (v ⊗ₜ[ℝ] w)) = _
  rw [contractionKernelSymmetricSquareInclusion_mk]
  rfl

/-- The original quotient contraction annihilates the full actual inclusion image.
Source: `prop:saturation`, subtracting a form on the covector kernel. -/
theorem contractionKernel_comp_inclusion_eq_zero (ξ : V →ₗ[ℝ] ℝ) :
    (contractionKernelQuotientMap ξ).comp
      (symmetricSquareLinearMap ξ.ker.subtype) = 0 := by
  apply (symmetricSquareRelations ξ.ker).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change contractionKernelQuotientMap ξ
    (symmetricSquareLinearMap ξ.ker.subtype (symmetricSquareProduct ξ.ker v w)) = 0
  rw [dictionaryMap_product, contractionKernelQuotientMap_product]
  change (1 / 2 : ℝ) • (ξ v.val • w.val + ξ w.val • v.val) = 0
  simp only [LinearMap.mem_ker.mp v.property, LinearMap.mem_ker.mp w.property,
    zero_smul, add_zero, smul_zero]

private def contractionDictionarySplit (ξ : V →ₗ[ℝ] ℝ) (e : V) (he : ξ e = 1) :
    (ξ.ker × ℝ) ≃ₗ[ℝ] V where
  toFun p := p.1.val + p.2 • e
  invFun v := (⟨v - ξ v • e, by simp [he]⟩, ξ v)
  left_inv := by
    rintro ⟨u, a⟩
    apply Prod.ext
    · apply Subtype.ext
      change (u.val + a • e) - ξ (u.val + a • e) • e = u.val
      simp [he, LinearMap.mem_ker.mp u.property]
    · change ξ (u.val + a • e) = a
      simp [he, LinearMap.mem_ker.mp u.property]
  right_inv v := sub_add_cancel v (ξ v • e)
  map_add' := by
    rintro ⟨u, a⟩ ⟨v, b⟩
    change (u.val + v.val) + (a + b) • e = (u.val + a • e) + (v.val + b • e)
    simp [add_smul, add_add_add_comm]
  map_smul' := by
    rintro c ⟨u, a⟩
    change c • u.val + (c * a) • e = c • (u.val + a • e)
    simp [smul_add, smul_smul]

private theorem contractionDictionarySplit_inclusion (ξ : V →ₗ[ℝ] ℝ)
    (e : V) (he : ξ e = 1) :
    supportedRankSplitSymmetricSquareInclusion (contractionDictionarySplit ξ e he) =
      symmetricSquareLinearMap ξ.ker.subtype := by
  apply (symmetricSquareRelations ξ.ker).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change supportedRankSplitSymmetricSquareInclusion (contractionDictionarySplit ξ e he)
    (symmetricSquareProduct ξ.ker v w) =
      symmetricSquareLinearMap ξ.ker.subtype (symmetricSquareProduct ξ.ker v w)
  rw [supportedRankSplitSymmetricSquareInclusion_product, dictionaryMap_product]
  simp [supportedRankSplitInclusion, contractionDictionarySplit]

private theorem contractionDictionary_exists_unit (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    ∃ e : V, ξ e = 1 := by
  have h : ∃ v : V, ξ v ≠ 0 := by
    by_contra! h
    apply hξ
    exact LinearMap.ext h
  obtain ⟨v, hv⟩ := h
  exact ⟨(ξ v)⁻¹ • v, by simp [hv]⟩

/-- The original kernel-subspace inclusion is genuinely injective.
Source: the exact binary splitting, specialized to a nonzero covector. -/
theorem contractionKernel_linearMap_injective (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    Function.Injective (symmetricSquareLinearMap ξ.ker.subtype) := by
  obtain ⟨e, he⟩ := contractionDictionary_exists_unit ξ hξ
  have h := (supported_rank_symmetric_square_splitting
    (contractionDictionarySplit ξ e he)).1
  rwa [contractionDictionarySplit_inclusion] at h

/-- The kernel of the SAME normalized contraction is exactly the actual image of
the original symmetric square of ker ξ. Source: `prop:saturation` contraction dictionary.

Proof: use the accepted general quotient splitting to write q=i(s)+e⊙v with ξe=1.
Contraction gives (v+ξ(v)e)/2. Its vanishing first forces ξ(v)=0 and then v=0.
No coordinate quotient, prescribed kernel equality or changed product is used. -/
theorem contractionKernel_ker_eq_range (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    LinearMap.ker (contractionKernelQuotientMap ξ) =
      LinearMap.range (symmetricSquareLinearMap ξ.ker.subtype) := by
  obtain ⟨e, he⟩ := contractionDictionary_exists_unit ξ hξ
  let d := contractionDictionarySplit ξ e he
  have hd (q : SymmetricSquare V) :
      ∃ (s : SymmetricSquare ξ.ker) (v : V),
        q = symmetricSquareLinearMap ξ.ker.subtype s + symmetricSquareProduct V e v := by
    refine ⟨(supportedRankSplitQuotientMap d q).1,
      (supportedRankSplitQuotientMap d q).2, ?_⟩
    have h := supportedRankSplitReconstruct_quotientMap d q
    change supportedRankSplitSymmetricSquareInclusion d
        (supportedRankSplitQuotientMap d q).1 +
      symmetricSquareProduct V (supportedRankSplitVector d)
        (supportedRankSplitQuotientMap d q).2 = q at h
    rw [contractionDictionarySplit_inclusion] at h
    simpa [supportedRankSplitVector, d, contractionDictionarySplit] using h.symm
  apply le_antisymm
  · intro q hq
    obtain ⟨s, v, rfl⟩ := hd q
    have hi := congrArg (fun f : SymmetricSquare ξ.ker →ₗ[ℝ] V ↦ f s)
      (contractionKernel_comp_inclusion_eq_zero ξ)
    change contractionKernelQuotientMap ξ (symmetricSquareLinearMap ξ.ker.subtype s) = 0 at hi
    have hz : (1 / 2 : ℝ) • (v + ξ v • e) = 0 := by
      simpa only [LinearMap.mem_ker, map_add, contractionKernelQuotientMap_product,
        he, one_smul, hi, zero_add] using hq
    have hv : v + ξ v • e = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
    have hξv : ξ v = 0 := by
      have ht := congrArg ξ hv
      simp only [map_add, map_smul, he, smul_eq_mul, mul_one, map_zero] at ht
      linarith
    have hv0 : v = 0 := by simpa [hξv] using hv
    exact ⟨s, by simp [hv0]⟩
  · rintro q ⟨s, rfl⟩
    exact congrArg (fun f : SymmetricSquare ξ.ker →ₗ[ℝ] V ↦ f s)
      (contractionKernel_comp_inclusion_eq_zero ξ)

/-- Good restriction injectivity equals actual contraction injectivity on SAME ker B.
Source: `prop:saturation`, the good-covector contraction criterion. -/
theorem linearSecondForm_restriction_injective_iff_contraction
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    Function.Injective (B.comp (symmetricSquareLinearMap ξ.ker.subtype)) ↔
      Function.Injective ((contractionKernelQuotientMap ξ).domRestrict B.ker) := by
  rw [LinearMap.injective_domRestrict_iff, contractionKernel_ker_eq_range ξ hξ,
    disjoint_comm, LinearMap.disjoint_ker_iff_injOn]
  have hi := contractionKernel_linearMap_injective ξ hξ
  constructor
  · intro h q hq r hr hqr
    obtain ⟨u, rfl⟩ := hq
    obtain ⟨v, rfl⟩ := hr
    exact congrArg (symmetricSquareLinearMap ξ.ker.subtype) (h hqr)
  · intro h u v huv
    apply hi
    exact h (LinearMap.mem_range_self _ u) (LinearMap.mem_range_self _ v) huv

/-- Dictionary for the SOLE original raw-B good-covector predicate.
Source: `defn:phase`, with the actual binary quotient and its literal kernel. -/
theorem linearSecondFormGoodCovector_iff_contraction
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : V →ₗ[ℝ] ℝ) :
    LinearSecondFormGoodCovector B ξ ↔
      ξ ≠ 0 ∧ Function.Injective
        ((contractionKernelQuotientMap ξ).domRestrict B.ker) := by
  constructor
  · rintro ⟨hξ, h⟩
    exact ⟨hξ, (linearSecondForm_restriction_injective_iff_contraction B ξ hξ).mp h⟩
  · rintro ⟨hξ, h⟩
    exact ⟨hξ, (linearSecondForm_restriction_injective_iff_contraction B ξ hξ).mpr h⟩

end GlobalEmbedding.Paper
