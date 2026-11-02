import GlobalEmbedding.Paper.SupportedRadicalClosedIncidence
import GlobalEmbedding.Paper.SupportedRankKernelComplementInverse
import GlobalEmbedding.Paper.NormalProjectionGramFormula
import GlobalEmbedding.Paper.SmoothFrameGramCoefficients

/-!+# Actual onto-kernel common-radical closedness

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1006. Reuse the accepted Gram projection identity and smooth frame coefficients for
the actual injective adjoint. The resulting actual kernel projection pulls compact radical
incidence back to the actual onto-operator subtype. No closedness premise is added.
-/

noncomputable section

open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

variable {S W : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The actual full adjoint is injective when the original operator is onto, by its accepted
actual kernel-complement equivalence. Source: `prop:supported-rank`, full-rank setting. -/
theorem supportedKernel_adjoint_injective (B : S →L[ℝ] W) (hB : Function.Surjective B) :
    Function.Injective B.adjoint := by
  intro x y h
  apply (supportedRankKernelAdjointEquiv B hB).injective
  exact Subtype.ext h

/-- The original actual kernel projection has the accepted genuine Gram formula.
Source: `prop:supported-rank`, smooth dependence of onto kernels. -/
theorem supportedKernel_projection_gram (B : S →L[ℝ] W) (hB : Function.Surjective B) :
    B.ker.starProjection = ContinuousLinearMap.id ℝ S -
      B.adjoint.comp ((B.comp B.adjoint).inverse.comp B) := by
  have h := (normal_projection_gram_formula B.adjoint
    (supportedKernel_adjoint_injective B hB)).2.2.2
  simpa only [ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.adjoint_adjoint] using h

/-- The actual kernel projection is continuous on the onto operators, using the already
accepted smooth Gram coefficient provider rather than differentiating another inverse.
Source: `prop:supported-rank`, actual kernel dependence. -/
theorem supportedKernel_projection_continuousOn :
    ContinuousOn (fun B : S →L[ℝ] W ↦ B.ker.starProjection)
      {B : S →L[ℝ] W | Function.Surjective B} := by
  let A : (S →L[ℝ] W) →L[ℝ] (W →L[ℝ] S) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := S) (F := W)).toContinuousLinearEquiv.toContinuousLinearMap
  have hA : ContMDiffOn 𝓘(ℝ, S →L[ℝ] W) 𝓘(ℝ, W →L[ℝ] S) ∞ A
      {B : S →L[ℝ] W | Function.Surjective B} :=
    A.contDiff.contMDiff.contMDiffOn
  have hC := smooth_frame_gram_coefficients A hA
    (fun B hB ↦ supportedKernel_adjoint_injective B hB)
  have hP := (continuousOn_const (c := ContinuousLinearMap.id ℝ S)).sub
    (hA.continuousOn.clm_comp hC.continuousOn)
  apply hP.congr
  intro B hB
  change B.ker.starProjection = ContinuousLinearMap.id ℝ S -
    B.adjoint.comp ((B.adjoint.adjoint.comp B.adjoint).inverse.comp B.adjoint.adjoint)
  simpa only [ContinuousLinearMap.adjoint_adjoint] using supportedKernel_projection_gram B hB

/-- Existence of an actual unit common radical of the original kernel is relatively closed
in the actual onto-operator subtype. Proof: compose the continuous actual kernel projector
with the given actual linear operator representation, then apply compact-radical incidence.
Source: `prop:supported-rank`, relative closedness before the literal support dictionary. -/
theorem supportedKernel_unit_radical_isClosed
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (M : S →L[ℝ] (V →L[ℝ] V)) :
    IsClosed {B : {B : S →L[ℝ] W | Function.Surjective B} |
      ∃ v : V, ‖v‖ = 1 ∧ ∀ q ∈ (B : S →L[ℝ] W).ker, M q v = 0} := by
  let Q : {B : S →L[ℝ] W | Function.Surjective B} → S →L[ℝ] (V →L[ℝ] V) :=
    fun B ↦ M.comp (B : S →L[ℝ] W).ker.starProjection
  have hP : Continuous (fun B : {B : S →L[ℝ] W | Function.Surjective B} ↦
      (B : S →L[ℝ] W).ker.starProjection) :=
    supportedKernel_projection_continuousOn.domRestrict
  have hQ : Continuous Q := continuous_const.clm_comp hP
  have hclosed := isClosed_hasUnitCommonRadical_preimage Q hQ
  convert hclosed using 1
  ext B
  constructor
  · rintro ⟨v, hv, hker⟩
    refine ⟨v, hv, fun q ↦ ?_⟩
    exact hker _ ((B : S →L[ℝ] W).ker.orthogonalProjectionOnto q).property
  · rintro ⟨v, hv, hQv⟩
    refine ⟨v, hv, ?_⟩
    intro q hq
    have h := hQv q
    change M ((B : S →L[ℝ] W).ker.starProjection q) v = 0 at h
    rwa [(B : S →L[ℝ] W).ker.starProjection_eq_self_iff.mpr hq] at h

end GlobalEmbedding.Paper
