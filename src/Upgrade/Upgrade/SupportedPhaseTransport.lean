import Upgrade.SupportedCoordinateTransport
import GlobalEmbedding.Paper.SaturationEuclideanModel

/-!
# Original good-covector and phase predicates under actual coordinates

This is the exact coordinate dictionary needed by phase protection. It reuses
the accepted canonical symmetric-square equivalence and its subtype law.
No auxiliary phase predicate, norm, kernel model, or rank classification is
introduced. Normal postcomposition only needs injectivity; source transport
uses an actual linear equivalence and transports the actual covector kernel.
-/

noncomputable section
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper

section Algebraic
variable {V V' W W' : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']

/-- An injective actual normal identification preserves every original good
covector, including its literal restricted second-form injectivity. -/
theorem linearSecondFormGoodCovector_postcomp_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (j : W →ₗ[ℝ] W')
    (hj : Function.Injective j) (ξ : V →ₗ[ℝ] ℝ) :
    LinearSecondFormGoodCovector (j.comp B) ξ ↔ LinearSecondFormGoodCovector B ξ := by
  constructor
  · rintro ⟨hne, hinj⟩
    refine ⟨hne, ?_⟩
    intro a b hab
    exact hinj (congrArg j hab)
  · rintro ⟨hne, hinj⟩
    refine ⟨hne, ?_⟩
    intro a b hab
    exact hinj (hj hab)

theorem linearSecondFormPhaseRegular_postcomp_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (j : W →ₗ[ℝ] W')
    (hj : Function.Injective j) :
    LinearSecondFormPhaseRegular (j.comp B) ↔ LinearSecondFormPhaseRegular B := by
  exact exists_congr fun ξ ↦ linearSecondFormGoodCovector_postcomp_iff B j hj ξ

/-- Pull an original good covector through the actual source equivalence.
Its actual kernel maps onto the original kernel, and the accepted square
subtype identity transports the restricted true form without changing it. -/
theorem linearSecondFormGoodCovector_source_coordinates
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : V' ≃ₗ[ℝ] V)
    (ξ : V →ₗ[ℝ] ℝ) (hξ : LinearSecondFormGoodCovector B ξ) :
    LinearSecondFormGoodCovector
      (B.comp (symmetricSquareLinearMap e.toLinearMap)) (ξ.comp e.toLinearMap) := by
  let K : Submodule ℝ V' := (ξ.comp e.toLinearMap).ker
  have hK : K.map e.toLinearMap = ξ.ker := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hv
      change ξ v = 0 at hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      change ξ (e (e.symm v)) = 0
      simpa only [e.apply_symm_apply] using hv
  let s : SymmetricSquare K ≃ₗ[ℝ] SymmetricSquare (K.map e.toLinearMap) :=
    saturationSymmetricSquareEquiv (e.submoduleMap K)
  have hsq : (symmetricSquareLinearMap e.toLinearMap).comp
      (symmetricSquareLinearMap K.subtype) =
        (symmetricSquareLinearMap (K.map e.toLinearMap).subtype).comp s.toLinearMap := by
    simpa only [s, saturationSymmetricSquareEquiv_toLinearMap] using
      saturationSymmetricSquareEquiv_subtype e K
  have hinj : Function.Injective
      (B.comp (symmetricSquareLinearMap (K.map e.toLinearMap).subtype)) := by
    rw [hK]
    exact hξ.2
  refine ⟨?_, ?_⟩
  · intro hz
    apply hξ.1
    apply LinearMap.ext
    intro v
    change ξ v = 0
    have hv := DFunLike.congr_fun hz (e.symm v)
    change ξ (e (e.symm v)) = 0 at hv
    simpa only [e.apply_symm_apply] using hv
  · intro a b hab
    apply s.injective
    apply hinj
    have ha := congrArg (fun L : SymmetricSquare K →ₗ[ℝ] SymmetricSquare V ↦ B (L a)) hsq
    have hb := congrArg (fun L : SymmetricSquare K →ₗ[ℝ] SymmetricSquare V ↦ B (L b)) hsq
    exact ha.symm.trans (hab.trans hb)

theorem linearSecondFormPhaseRegular_source_coordinates
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : V' ≃ₗ[ℝ] V)
    (hB : LinearSecondFormPhaseRegular B) :
    LinearSecondFormPhaseRegular (B.comp (symmetricSquareLinearMap e.toLinearMap)) := by
  obtain ⟨ξ, hξ⟩ := hB
  exact ⟨ξ.comp e.toLinearMap, linearSecondFormGoodCovector_source_coordinates B e ξ hξ⟩

/-- Surjectivity is also unchanged by an actual source equivalence. -/
theorem surjective_symmetricSquare_source_coordinates_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : V' ≃ₗ[ℝ] V) :
    Function.Surjective (B.comp (symmetricSquareLinearMap e.toLinearMap)) ↔
      Function.Surjective B := by
  have hs : Function.Surjective (symmetricSquareLinearMap e.toLinearMap) := by
    rw [← saturationSymmetricSquareEquiv_toLinearMap e]
    exact (saturationSymmetricSquareEquiv e).surjective
  constructor
  · intro h y
    obtain ⟨q, hq⟩ := h y
    exact ⟨symmetricSquareLinearMap e.toLinearMap q, hq⟩
  · intro h
    exact h.comp hs

end Algebraic

section NormedSource
variable {V V' W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [AddCommGroup W] [Module ℝ W]

/-- The original phase predicate is equivalent in actual invertible source
coordinates. This can be applied to the proved inverse atlas differential. -/
theorem linearSecondFormPhaseRegular_source_coordinates_iff
    (B : SymmetricSquare V →ₗ[ℝ] W) (e : V' ≃L[ℝ] V) :
    LinearSecondFormPhaseRegular (B.comp (symmetricSquareLinearMap e.toLinearMap)) ↔
      LinearSecondFormPhaseRegular B := by
  constructor
  · intro h
    have hback := linearSecondFormPhaseRegular_source_coordinates
      (B.comp (symmetricSquareLinearMap e.toLinearMap)) e.symm.toLinearEquiv h
    have heq : (B.comp (symmetricSquareLinearMap e.toLinearMap)).comp
        (symmetricSquareLinearMap e.symm.toLinearMap) = B := by
      apply LinearMap.ext
      intro q
      change B (symmetricSquareLinearMap e.toLinearMap
        (symmetricSquareLinearMap e.symm.toLinearMap q)) = B q
      have he : symmetricSquareLinearMap e.toLinearMap =
          symmetricSquareMap e.toContinuousLinearMap :=
        symmetric_square_linear_map_eq e.toContinuousLinearMap
      have he' : symmetricSquareLinearMap e.symm.toLinearMap =
          symmetricSquareMap e.symm.toContinuousLinearMap :=
        symmetric_square_linear_map_eq e.symm.toContinuousLinearMap
      rw [he, he']
      exact congrArg B (symmetricSquareMap_symm e.symm q)
    rwa [heq] at hback
  · exact linearSecondFormPhaseRegular_source_coordinates B e.toLinearEquiv

end NormedSource

#print axioms linearSecondFormGoodCovector_postcomp_iff
#print axioms linearSecondFormPhaseRegular_postcomp_iff
#print axioms linearSecondFormGoodCovector_source_coordinates
#print axioms linearSecondFormPhaseRegular_source_coordinates
#print axioms surjective_symmetricSquare_source_coordinates_iff
#print axioms linearSecondFormPhaseRegular_source_coordinates_iff

end GlobalEmbedding.Upgrade
