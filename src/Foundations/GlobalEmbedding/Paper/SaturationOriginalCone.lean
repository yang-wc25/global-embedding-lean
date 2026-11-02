import GlobalEmbedding.Paper.SaturationLinearImage
import GlobalEmbedding.Paper.SaturationOriginalData
import GlobalEmbedding.Paper.ContractionKernelDictionary
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Identifying the literal original cone carrier

Source: original `prop:saturation`, lines971–978. This honest dictionary core uses
an actual linear realization of the SAME contraction and actual openness/scaling of
the sole good predicate. The full original target must instantiate those dictionary
facts; they are not new final hypotheses. No original saturation data are redefined.
-/

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The ORIGINAL existential-full-open-positive-cone carrier equals the actual
contraction intersection. All linear/open/conical dictionary inputs are honest
intermediate facts to be instantiated from the actual contraction providers.
Source: original `prop:saturation`, polynomial continuation of the cone condition. -/
theorem saturation_originalSet_eq_intersection_of_linear_family
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (T : (V →L[ℝ] ℝ) →ₗ[ℝ] (SymmetricSquare V →ₗ[ℝ] V))
    (hT : ∀ ξ, T ξ = contractionKernelQuotientMap ξ.toLinearMap)
    (hopen : IsOpen {ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap})
    (hcone : ∀ t : ℝ, 0 < t → ∀ ξ : V →L[ℝ] ℝ,
      LinearSecondFormGoodCovector B ξ.toLinearMap →
      LinearSecondFormGoodCovector B (t • ξ).toLinearMap) :
    originalSaturationSet B = (saturationContractionIntersection B : Set (SymmetricSquare V)) := by
  ext P
  constructor
  · rintro ⟨C, hCopen, hCne, _, _, hlocal⟩
    let A := T.domRestrict₂ B.ker
    let b := T.flip P
    have hc : ∀ ξ ∈ C, ∃ k : B.ker, A ξ k = b ξ := by
      intro ξ hξ
      obtain ⟨q, hq, heq⟩ := Submodule.mem_map.mp (hlocal ξ hξ)
      refine ⟨⟨q, hq⟩, ?_⟩
      change T ξ q = T ξ P
      rw [hT]
      exact heq
    have hp := saturation_linear_family_image_of_open A b C hCopen hCne hc
    apply (Submodule.mem_iInf _).mpr
    intro ξ
    have hi : Function.Injective (A ξ.val) := by
      change Function.Injective ((T ξ.val).domRestrict B.ker)
      rw [hT]
      exact ((linearSecondFormGoodCovector_iff_contraction B ξ.val.toLinearMap).mp
        ξ.property).2
    obtain ⟨k, hk⟩ := hp ξ.val hi
    refine Submodule.mem_map.mpr ⟨k.val, k.property, ?_⟩
    change T ξ.val k.val = T ξ.val P at hk
    simpa only [hT] using hk
  · intro hP
    obtain ⟨ξ, hξ⟩ := (saturation_phaseRegular_iff_continuous_covector B).mp hB
    refine ⟨{ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap},
      hopen, ⟨ξ, hξ⟩, hcone, (fun _ h ↦ h), ?_⟩
    intro η hη
    exact (Submodule.mem_iInf _).mp hP ⟨η, hη⟩

/-- Native finite-dimensional coordinates transport actual injective-family density.
Source: original `prop:saturation`, intersecting a maximal-rank open region with
the actual full-rank kernel-evaluation locus. No density hypothesis is supplied. -/
theorem saturation_linear_family_injective_meets_open
    {D K E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [AddCommGroup K] [Module ℝ K] [FiniteDimensional ℝ K]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : D →ₗ[ℝ] K →ₗ[ℝ] E) (hinj : ∃ x, Function.Injective (A x))
    (U : Set D) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, Function.Injective (A x) := by
  let db := Module.finBasis ℝ D
  let kb := Module.finBasis ℝ K
  let eb := Module.finBasis ℝ E
  let e := db.equivFunL
  let Ac := ((LinearMap.toMatrix kb eb).toLinearMap.comp A).comp e.symm.toLinearMap
  have hm (x : Fin (Module.finrank ℝ D) → ℝ) (v : K) :
      (Ac x).mulVec (kb.equivFun v) = eb.equivFun (A (e.symm x) v) := by
    change (LinearMap.toMatrix kb eb (A (e.symm x))).mulVec (kb.equivFun v) = _
    simpa only [Module.Basis.equivFun_apply] using
      (A (e.symm x)).toMatrix_mulVec_repr kb eb v
  have hc (x : Fin (Module.finrank ℝ D) → ℝ)
      (hx : Function.Injective (A (e.symm x))) : Function.Injective (Ac x).mulVec := by
    intro u v huv
    apply kb.equivFun.symm.injective
    apply hx
    apply eb.equivFun.injective
    have hu := hm x (kb.equivFun.symm u)
    have hv := hm x (kb.equivFun.symm v)
    simp only [kb.equivFun.apply_symm_apply] at hu hv
    exact hu.symm.trans (huv.trans hv)
  have hi : ∃ x, Function.Injective (Ac x).mulVec := by
    obtain ⟨x, hx⟩ := hinj
    exact ⟨e x, hc (e x) (by simpa only [e.symm_apply_apply] using hx)⟩
  have hn : (e.symm ⁻¹' U).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, by simpa only [Set.mem_preimage, e.symm_apply_apply] using hx⟩
  obtain ⟨x, hx, hax⟩ := saturation_linear_injective_meets_open Ac hi (e.symm ⁻¹' U)
    (hU.preimage e.symm.continuous) hn
  refine ⟨e.symm x, hx, ?_⟩
  intro u v huv
  apply kb.equivFun.injective
  apply hax
  rw [hm, hm, huv]

/-- The actual original good covectors meet every nonempty full-dual open set.
Zero is excluded using native real-module punctured density, including ker B=0.
The actual linear-realization input is an intermediate dictionary fact only.
Source: original `prop:saturation`, global maximal evaluation bound. -/
theorem saturation_good_meets_open_of_linear_family
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : LinearSecondFormPhaseRegular B)
    (T : (V →L[ℝ] ℝ) →ₗ[ℝ] (SymmetricSquare V →ₗ[ℝ] V))
    (hT : ∀ ξ, T ξ = contractionKernelQuotientMap ξ.toLinearMap)
    (U : Set (V →L[ℝ] ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ξ ∈ U, LinearSecondFormGoodCovector B ξ.toLinearMap := by
  obtain ⟨ξ₀, hξ₀⟩ := (saturation_phaseRegular_iff_continuous_covector B).mp hB
  have hξ₀ne : ξ₀ ≠ 0 := by
    intro hz
    exact hξ₀.1 (by rw [hz]; rfl)
  have : Nontrivial (V →L[ℝ] ℝ) := ⟨⟨ξ₀, 0, hξ₀ne⟩⟩
  let A := T.domRestrict₂ B.ker
  have hi : ∃ ξ, Function.Injective (A ξ) := by
    refine ⟨ξ₀, ?_⟩
    change Function.Injective ((T ξ₀).domRestrict B.ker)
    rw [hT]
    exact ((linearSecondFormGoodCovector_iff_contraction B ξ₀.toLinearMap).mp hξ₀).2
  have hn : (U ∩ ({0}ᶜ : Set (V →L[ℝ] ℝ))).Nonempty :=
    (dense_compl_singleton (0 : V →L[ℝ] ℝ)).inter_open_nonempty U hU hne
  obtain ⟨ξ, hξ, hx⟩ := saturation_linear_family_injective_meets_open A hi
    (U ∩ {0}ᶜ) (hU.inter isOpen_compl_singleton) hn
  refine ⟨ξ, hξ.1, (linearSecondFormGoodCovector_iff_contraction B ξ.toLinearMap).mpr
    ⟨?_, ?_⟩⟩
  · intro hz
    have hzero : ξ = 0 := by ext v; exact congrArg (fun f ↦ f v) hz
    exact hξ.2 hzero
  · change Function.Injective ((T ξ).domRestrict B.ker) at hx
    simpa only [hT] using hx

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_originalSet_eq_intersection_of_linear_family
#print axioms GlobalEmbedding.Paper.saturation_linear_family_injective_meets_open
#print axioms GlobalEmbedding.Paper.saturation_good_meets_open_of_linear_family
