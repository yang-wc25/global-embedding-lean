import GlobalEmbedding.Paper.BalancedPairingColumns
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Actual directional product rules for the balanced metric calculation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 413–415.
DAG node: `balanced-directional-calculus`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual real directional derivative, with Mathlib's canonical target identification. -/
noncomputable def balancedScalarDirectionalDerivative (q : M → ℝ)
    (D : ∀ x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I q x (D x)

/-- Taking an actual directional derivative along a smooth field preserves smoothness.
The native tangent map is smooth; compose it with the native smooth section and then
the genuine smooth fiber projection of the target Euclidean tangent bundle. -/
theorem balanced_directional_contMDiff [IsManifold I ∞ M] {N : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (D : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (balancedDirectionalDerivative P D) := by
  exact (contMDiff_snd_tangentBundle_modelSpace (EuclideanSpace ℝ (Fin N))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N))).comp
      ((hP.contMDiff_tangentMap (m := ∞) (by simp)).comp D.contMDiff)

/-- Actual directional derivatives respect addition by Mathlib's vector-valued
manifold derivative addition rule, evaluated at the actual field. -/
theorem balanced_directional_add {N : ℕ}
    (f g : M → EuclideanSpace ℝ (Fin N))
    (D : ∀ x : M, TangentSpace I x) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) g x) :
    balancedDirectionalDerivative (f + g) D x =
      balancedDirectionalDerivative f D x + balancedDirectionalDerivative g D x := by
  change mvfderiv I (f + g) x (D x) =
    mvfderiv I f x (D x) + mvfderiv I g x (D x)
  rw [mvfderiv_add hf hg]
  rfl

/-- Actual real directional derivatives respect negation, including nondifferentiable
functions under Mathlib's zero-derivative convention. -/
theorem balanced_scalar_directional_neg (q : M → ℝ)
    (D : ∀ x : M, TangentSpace I x) (x : M) :
    balancedScalarDirectionalDerivative (-q) D x =
      -balancedScalarDirectionalDerivative q D x := by
  unfold balancedScalarDirectionalDerivative
  rw [mvfderiv_neg]
  rfl

/-- The genuine manifold product rule for the Euclidean inner product along a field.
Compose the normed inner-product map with the actual pair `(f,g)`, use the manifold
chain rule and the product derivative, then Mathlib's Fréchet inner-product rule.
No differentiation of an abstract formal derivation is assumed. -/
theorem balanced_directional_inner {N : ℕ}
    (f g : M → EuclideanSpace ℝ (Fin N))
    (D : ∀ x : M, TangentSpace I x) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) g x) :
    balancedScalarDirectionalDerivative (fun y ↦ inner ℝ (f y) (g y)) D x =
      inner ℝ (f x) (balancedDirectionalDerivative g D x) +
      inner ℝ (balancedDirectionalDerivative f D x) (g x) := by
  let b : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) → ℝ :=
    fun z ↦ inner ℝ z.1 z.2
  have hb : DifferentiableAt ℝ b (f x, g x) :=
    differentiableAt_fst.inner ℝ differentiableAt_snd
  have hc := mfderiv_comp_apply x hb.mdifferentiableAt (hf.prodMk_space hg) (D x)
  rw [mfderiv_eq_fderiv] at hc
  have hd : fderiv ℝ b (f x, g x) =
      (innerSL ℝ (f x)).comp (ContinuousLinearMap.snd ℝ _ _) +
      (innerSL ℝ (g x)).comp (ContinuousLinearMap.fst ℝ _ _) := by
    apply ContinuousLinearMap.ext
    intro z
    simpa only [add_apply, ContinuousLinearMap.comp_apply, fderiv_fst, fderiv_snd,
      innerSL_apply_apply, real_inner_comm] using
      (fderiv_inner_apply ℝ (x := (f x, g x)) differentiableAt_fst
        differentiableAt_snd z)
  rw [hd] at hc
  have hprod :
      tangentSpaceCastModel
        𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) (f x, g x)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))
          (fun y ↦ (f y, g y)) x (D x)) =
        (balancedDirectionalDerivative f D x, balancedDirectionalDerivative g D x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, mfderiv_prodMk hf hg]
    rfl
  have hc' := congrArg (tangentSpaceCastModel 𝓘(ℝ, ℝ) (b (f x, g x))) hc
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply, add_apply,
    ] at hc'
  change balancedScalarDirectionalDerivative
    (fun y ↦ inner ℝ (f y) (g y)) D x =
      inner ℝ (f x)
        ((tangentSpaceCastModel
          𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) (f x, g x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))
            (fun y ↦ (f y, g y)) x (D x))).2) +
      inner ℝ (g x)
        ((tangentSpaceCastModel
          𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) (f x, g x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N))
            (fun y ↦ (f y, g y)) x (D x))).1) at hc'
  rw [hprod] at hc'
  simpa only [balancedScalarDirectionalDerivative, mvfderiv, b, Function.comp_apply,
    NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    real_inner_comm] using hc'


end GlobalEmbedding.Paper
