import GlobalEmbedding.Paper.SaturationEuclideanModel
import GlobalEmbedding.Paper.SupportedLocusLocalEquations

/-! Coordinate invariance of the literal Good predicate on the full original
binary symmetric quotient. The proof uses the actual kernel, its image under
the actual tangent equivalence, and the accepted symmetric-square subtype law. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Function
namespace GlobalEmbedding.Continuation
variable {E F V W : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem jointSecondary_good_injective_codomain
    (B : SymmetricSquare E →ₗ[ℝ] V) (J : V →ₗ[ℝ] W) (hJ : Injective J)
    (xi : E →ₗ[ℝ] ℝ) :
    LinearSecondFormGoodCovector (J.comp B) xi ↔ LinearSecondFormGoodCovector B xi := by
  constructor
  · rintro ⟨hx,hb⟩
    exact ⟨hx,fun a b hab => hb (congrArg J hab)⟩
  · rintro ⟨hx,hb⟩
    exact ⟨hx,fun a b hab => hb (hJ hab)⟩

theorem jointSecondary_good_pullback_equiv
    (B : SymmetricSquare F →ₗ[ℝ] V) (e : E ≃ₗ[ℝ] F) (xi : F →ₗ[ℝ] ℝ) :
    LinearSecondFormGoodCovector (B.comp (symmetricSquareLinearMap e.toLinearMap))
      (xi.comp e.toLinearMap) ↔ LinearSecondFormGoodCovector B xi := by
  let U := (xi.comp e.toLinearMap).ker
  have hker : U.map e.toLinearMap = xi.ker := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro hv
      change xi v = 0 at hv
      refine ⟨e.symm v,?_,e.apply_symm_apply v⟩
      change xi (e (e.symm v)) = 0
      simpa only [e.apply_symm_apply] using hv
  let C := saturationSymmetricSquareEquiv (e.submoduleMap U)
  have hcomm : (B.comp (symmetricSquareLinearMap e.toLinearMap)).comp
      (symmetricSquareLinearMap U.subtype) =
      (B.comp (symmetricSquareLinearMap (U.map e.toLinearMap).subtype)).comp C.toLinearMap := by
    rw [← saturationSymmetricSquareEquiv_toLinearMap e,LinearMap.comp_assoc,
      saturationSymmetricSquareEquiv_subtype,← LinearMap.comp_assoc]
  have hi : Injective ((B.comp (symmetricSquareLinearMap e.toLinearMap)).comp
      (symmetricSquareLinearMap U.subtype)) ↔
      Injective (B.comp (symmetricSquareLinearMap (U.map e.toLinearMap).subtype)) := by
    rw [hcomm]
    constructor
    · intro h a b hab
      apply C.symm.injective
      apply h
      simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using hab
    · intro h
      exact h.comp C.injective
  have hn : xi.comp e.toLinearMap ≠ 0 ↔ xi ≠ 0 := by
    constructor
    · intro h hz
      exact h (by rw [hz]; rfl)
    · intro h hz
      apply h
      ext v
      have hh := DFunLike.congr_fun hz (e.symm v)
      simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,e.apply_symm_apply,
        LinearMap.zero_apply] using hh
  unfold LinearSecondFormGoodCovector
  change (xi.comp e.toLinearMap ≠ 0 ∧ Injective ((B.comp (symmetricSquareLinearMap e.toLinearMap)).comp
    (symmetricSquareLinearMap U.subtype))) ↔ _
  rw [hn,hi,hker]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_good_injective_codomain
#print axioms GlobalEmbedding.Continuation.jointSecondary_good_pullback_equiv
