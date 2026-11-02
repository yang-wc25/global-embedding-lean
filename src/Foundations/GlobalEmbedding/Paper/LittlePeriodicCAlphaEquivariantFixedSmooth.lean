import GlobalEmbedding.Paper.BalancedImplicitBranch
import GlobalEmbedding.Paper.LittlePeriodicCAlphaComplete
import GlobalEmbedding.Paper.LittlePeriodicCAlphaQuadraticConjugation
import GlobalEmbedding.Paper.LittlePeriodicCAlphaJointSmooth
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateFixedEquation

/-!
# Genuine joint smoothness of actual equivariant little Hölder fixed families

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-equivariant-fixed-joint-smooth`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- An actual equivariant little Hölder quadratic fixed family is jointly smooth.

Translate the actual fixed equation. Equivariance and inverse translations give the
translated fixed equation, while actual linearization conjugacy preserves its strict
smallness. Apply the proved Banach implicit-branch theorem on the open product parameter
set, with the original complete little spaces. Bounded evaluation at zero then recovers
joint smoothness of the actual lift. No continuity of the selected fixed family is assumed.
The paper-specific Q construction and bundle transitions remain separate prerequisites.
Source: the local translation argument in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_equivariant_fixed_joint_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a M N k : ℕ} {α : ℝ} (U : Set E) (hU : IsOpen U)
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a M k α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (f : E → LittlePeriodicCAlphaFunction a N k α)
    (A : E → LittlePeriodicCAlphaFunction a M k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α)
    (v : E → LittlePeriodicCAlphaFunction a N k α)
    (hf : ContDiffOn ℝ ∞ (fun z : E × EuclideanSpace ℝ (Fin a) ↦
      littlePeriodicCAlphaTranslateIsometry z.2 (f z.1)) (U ×ˢ univ))
    (hA : ContDiffOn ℝ ∞ (fun z : E × EuclideanSpace ℝ (Fin a) ↦
      (littlePeriodicCAlphaTranslateIsometry z.2).toContinuousLinearMap.comp
        ((A z.1).comp
          (littlePeriodicCAlphaTranslateIsometry (-z.2)).toContinuousLinearMap)) (U ×ˢ univ))
    (hfixed : ∀ p ∈ U, v p = f p + A p (Q (v p) (v p)))
    (hsmall : ∀ p ∈ U, ‖(2 : ℝ) • (A p).comp (Q (v p))‖ < 1) :
    ContDiffOn ℝ ∞ (fun z : E × EuclideanSpace ℝ (Fin a) ↦
      littlePeriodicCAlphaTranslateIsometry z.2 (v z.1)) (U ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : E × EuclideanSpace ℝ (Fin a) ↦
      (v z.1).val.toFun z.2) (U ×ˢ univ) := by
  let ft := fun z : E × EuclideanSpace ℝ (Fin a) ↦
    littlePeriodicCAlphaTranslateIsometry z.2 (f z.1)
  let At := fun z : E × EuclideanSpace ℝ (Fin a) ↦
    (littlePeriodicCAlphaTranslateIsometry z.2).toContinuousLinearMap.comp
      ((A z.1).comp
        (littlePeriodicCAlphaTranslateIsometry (-z.2)).toContinuousLinearMap)
  let w := fun z : E × EuclideanSpace ℝ (Fin a) ↦
    littlePeriodicCAlphaTranslateIsometry z.2 (v z.1)
  have hfix : ∀ z ∈ U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a))),
      w z = ft z + At z (Q (w z) (w z)) := by
    intro z hz
    exact littlePeriodicCAlpha_translate_fixed_equation Q hQτ (A z.1) (f z.1) (v z.1)
      z.2 (hfixed z.1 hz.1)
  have hs : ∀ z ∈ U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a))),
      ‖(2 : ℝ) • (At z).comp (Q (w z))‖ < 1 := by
    intro z hz
    exact (littlePeriodicCAlpha_quadratic_conjugation Q hQτ (A z.1) z.2 (v z.1)).2.trans_lt
      (hsmall z.1 hz.1)
  have hw : ContDiffOn ℝ ∞ w (U ×ˢ univ) :=
    (balanced_fixed_implicit_branch (U ×ˢ univ) (hU.prod isOpen_univ) Q hQsym ft At w
      hf hA hfix hs).1
  exact ⟨hw, littlePeriodicCAlpha_joint_smooth_of_orbit U v hw⟩

#print axioms littlePeriodicCAlpha_equivariant_fixed_joint_smooth

end GlobalEmbedding.Paper
