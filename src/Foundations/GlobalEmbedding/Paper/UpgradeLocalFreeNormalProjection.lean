import GlobalEmbedding.Paper.GoodCovector
import GlobalEmbedding.Paper.SupportedRankLegalVariation
import GlobalEmbedding.Paper.SmoothImmersionNormalProjection
import GlobalEmbedding.Paper.SmoothFrameGramCoefficients
import GlobalEmbedding.Paper.NormalProjectionGramFormula

/-! Actual PN-PA assembly in original main.tex1053–1057.
DAG: upgrade-local-free-normal-projection. The finite coefficient and kernel
coordinate data are INTERNAL constructed inputs, discharged in the locked full
local-wave consumer. No new projection or bundle theory is introduced. -/

noncomputable section
open Manifold Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual normal projection minus the actual restricted-image projection
extends any original legal normal value as a smooth legal normal section on U.
This is the internal same-data projection assembly, not an extra hypothesis on
the full local-wave theorem. Its A and C are constructed from actual trueB.

Proof: the literal coefficient identity puts range A inside actual normalSpace.
Reuse the accepted manifold Gram coefficients and actual Gram projection formula
to prove the actual range projection PA smooth. Native nested projection gives
PA PN=PA, so PN(nu)-PA(nu) is normal and perpendicular to the actual restricted
image. The supplied legal value is fixed at x since PN fixes it and PA kills it.
Define the actual normal section by this value on U and zero elsewhere. Its
ambient smoothness and legality are asserted only on U. All existing structures,
the actual F/trueB/normalSpace and original legalValueSpace are retained; nu may
be zero. Source: extend free fields by smooth projection, main.tex1053–1057. -/
theorem upgrade_exists_local_free_normal_field
    {E H M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (U : Set M) (x : M) (hx : x ∈ U) (psi : M → ℝ)
    (A : M → D →L[ℝ] EuclideanSpace ℝ (Fin N))
    (hA : ContMDiffOn I 𝓘(ℝ, D →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞ A U)
    (hinj : ∀ z ∈ U, Function.Injective (A z))
    (hC : ∀ z ∈ U, ∃ C : D ≃ₗ[ℝ] SymmetricSquare (mfderiv I 𝓘(ℝ, ℝ) psi z).ker,
      ∀ d, A z d = (trueSecondForm F hF z
        (symmetricSquareLinearMap (mfderiv I 𝓘(ℝ, ℝ) psi z).ker.subtype (C d)) :
          EuclideanSpace ℝ (Fin N)))
    (nu : normalSpace (I := I) F x)
    (hnu : nu ∈ supportedRankLegalValueSpace (trueSecondForm F hF x)
      (mfderiv I 𝓘(ℝ, ℝ) psi x).toLinearMap) :
    ∃ v : ∀ z : M, normalSpace (I := I) F z,
      v x = nu ∧
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun z ↦ (v z : EuclideanSpace ℝ (Fin N))) U ∧
      ∀ z ∈ U, v z ∈ supportedRankLegalValueSpace (trueSecondForm F hF z)
        (mfderiv I 𝓘(ℝ, ℝ) psi z).toLinearMap := by
  classical
  let R (z : M) := LinearMap.range (A z).toLinearMap
  have hrange (z : M) (hz : z ∈ U) : R z ≤ normalSpace (I := I) F z := by
    rintro w ⟨d, rfl⟩
    obtain ⟨C, hCd⟩ := hC z hz
    change A z d ∈ normalSpace (I := I) F z
    rw [hCd d]
    exact (trueSecondForm F hF z _).property
  have hPAeq (z : M) (hz : z ∈ U) :
      (R z).starProjection = (A z).comp
        (((A z).adjoint.comp (A z)).inverse.comp (A z).adjoint) := by
    have h := (normal_projection_gram_formula (A z) (hinj z hz)).2.2.2
    rw [Submodule.starProjection_orthogonal] at h
    exact sub_right_inj.mp h
  have hPA : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) ∞ (fun z ↦ (R z).starProjection) U := by
    apply (hA.clm_comp (smooth_frame_gram_coefficients A hA hinj)).congr
    intro z hz
    exact hPAeq z hz
  let raw (z : M) : EuclideanSpace ℝ (Fin N) :=
    (normalSpace (I := I) F z).starProjection nu - (R z).starProjection nu
  have hraw : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ raw U :=
    ((smooth_immersion_normal_projection F hF himm).contMDiffOn.clm_apply
      (contMDiffOn_const (c := (nu : EuclideanSpace ℝ (Fin N))))).sub
        (hPA.clm_apply (contMDiffOn_const (c := (nu : EuclideanSpace ℝ (Fin N)))))
  have hn (z : M) (hz : z ∈ U) : raw z ∈ normalSpace (I := I) F z :=
    (normalSpace (I := I) F z).sub_mem
      ((normalSpace (I := I) F z).starProjection_apply_mem nu)
      (hrange z hz ((R z).starProjection_apply_mem nu))
  have hp (z : M) (hz : z ∈ U) : raw z ∈ (R z)ᗮ := by
    have h := DFunLike.congr_fun
      (Submodule.starProjection_comp_starProjection_of_le (hrange z hz))
      (nu : EuclideanSpace ℝ (Fin N))
    change (R z).starProjection ((normalSpace (I := I) F z).starProjection nu) =
      (R z).starProjection nu at h
    dsimp only [raw]
    rw [← h]
    exact Submodule.sub_starProjection_mem_orthogonal _
  have hnuR : (nu : EuclideanSpace ℝ (Fin N)) ∈ (R x)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro w ⟨d, rfl⟩
    obtain ⟨C, hCd⟩ := hC x hx
    change inner ℝ (A x d) (nu : EuclideanSpace ℝ (Fin N)) = 0
    rw [hCd d]
    exact (supportedRank_mem_legalValueSpace_iff _ _ _).mp hnu (C d)
  have hrawx : raw x = (nu : EuclideanSpace ℝ (Fin N)) := by
    have hzero : (R x).starProjection (nu : EuclideanSpace ℝ (Fin N)) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff (R x)).mpr hnuR
    simp only [raw, Submodule.starProjection_mem_subspace_eq_self, hzero, sub_zero]
  let v (z : M) : normalSpace (I := I) F z := if hz : z ∈ U then ⟨raw z, hn z hz⟩ else 0
  have hv (z : M) (hz : z ∈ U) : (v z : EuclideanSpace ℝ (Fin N)) = raw z := by
    simp only [v, dite_eq_left hz]
  refine ⟨v, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [hv x hx, hrawx]
  · apply hraw.congr
    intro z hz
    exact hv z hz
  · intro z hz
    apply (supportedRank_mem_legalValueSpace_iff _ _ _).mpr
    intro q
    change inner ℝ (trueSecondForm F hF z
      (symmetricSquareLinearMap (mfderiv I 𝓘(ℝ, ℝ) psi z).ker.subtype q) :
        EuclideanSpace ℝ (Fin N)) (v z : EuclideanSpace ℝ (Fin N)) = 0
    rw [hv z hz]
    apply (Submodule.mem_orthogonal _ _).mp (hp z hz)
    obtain ⟨C, hCd⟩ := hC z hz
    obtain ⟨d, rfl⟩ := C.surjective q
    exact ⟨d, hCd d⟩

#print axioms upgrade_exists_local_free_normal_field

end GlobalEmbedding.Paper
