import GlobalEmbedding.Paper.FreeGramRightInverse
import GlobalEmbedding.Paper.TrueSecondFormConnection
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Actual coordinate Gram coefficients and the original normal Hessian

Source: `main.tex`, lem:increments617–629. W2.
Every frame and Hessian below comes from the SAME actual F. Inverse, projection
and true-second-form facts are reused from accepted providers, not reconstructed.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Lowering the actual reconstructed displacement gives exactly the original u.
Only the accepted actual Gram inverse cancellation and native adjoint kernel
description of the true normal space are used. Source: Z=dF(g^-1u)+v in617–620. -/
theorem increments_gram_reconstruction_lowering {n N : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x u : EuclideanSpace ℝ (Fin n)) (ν : EuclideanSpace ℝ (Fin N))
    (hA : Function.Injective (fderiv ℝ F x))
    (hν : ν ∈ (LinearMap.range (fderiv ℝ F x).toLinearMap)ᗮ) :
    let A := fderiv ℝ F x
    A.adjoint (A ((A.adjoint.comp A).inverse u) + ν) = u := by
  let A := fderiv ℝ F x
  have hn : A.adjoint ν = 0 := by
    rwa [ContinuousLinearMap.orthogonal_range] at hν
  have hi := (frame_gram_positive_invertible A hA).2.2
  change A.adjoint (A ((A.adjoint.comp A).inverse u) + ν) = u
  rw [map_add, hn, add_zero]
  exact hi.self_apply_inverse u

/-- The actual Hessian paired with dF(g^-1u)+v splits into the actual Christoffel
coefficient and actual normal second-form pairing. Reuse the accepted self-adjoint
Gram inverse and native orthogonal projection characterization, with no new inverse
or normal construction. Source: the geometric first variation in617–620. -/
theorem increments_hessian_pairing_gram_normal {n N : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v w u : EuclideanSpace ℝ (Fin n)) (ν : EuclideanSpace ℝ (Fin N))
    (hA : Function.Injective (fderiv ℝ F x))
    (hν : ν ∈ (LinearMap.range (fderiv ℝ F x).toLinearMap)ᗮ) :
    let A := fderiv ℝ F x
    let H := fderiv ℝ (fderiv ℝ F) x v w
    inner ℝ H (A ((A.adjoint.comp A).inverse u) + ν) =
      inner ℝ ((A.adjoint.comp A).inverse (A.adjoint H)) u +
      inner ℝ ((LinearMap.range A.toLinearMap)ᗮ.starProjection H) ν := by
  let A := fderiv ℝ F x
  let H := fderiv ℝ (fderiv ℝ F) x v w
  let G := A.adjoint.comp A
  have hself : G.inverse.adjoint = G.inverse := freeGramInverse_adjoint A hA
  have ht := ContinuousLinearMap.adjoint_inner_left G.inverse u (A.adjoint H)
  rw [hself] at ht
  have ha := ContinuousLinearMap.adjoint_inner_left A (G.inverse u) H
  have hn := (LinearMap.range A.toLinearMap)ᗮ.starProjection_inner_eq_zero H ν hν
  rw [inner_sub_left] at hn
  change inner ℝ H (A (G.inverse u) + ν) =
    inner ℝ (G.inverse (A.adjoint H)) u +
      inner ℝ ((LinearMap.range A.toLinearMap)ᗮ.starProjection H) ν
  rw [inner_add_right]
  linarith

/-- The Gram tangential Hessian coefficient is the actual induced Christoffel
coefficient: it satisfies the lower Koszul formula for the SAME induced metric.
Native actual metric differentiation and C2 Hessian symmetry give the three
terms; accepted Gram inverse cancellation identifies the coefficient. It is not
an arbitrary supplied connection. Source: Gamma in the original mode system. -/
theorem increments_coordinate_christoffel_koszul {n N : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v w z : EuclideanSpace ℝ (Fin n)) (hF : ContDiffAt ℝ 2 F x)
    (hA : Function.Injective (fderiv ℝ F x)) :
    let A := fderiv ℝ F x
    let G := A.adjoint.comp A
    let H := fderiv ℝ (fderiv ℝ F) x v w
    2 * inner ℝ (G (G.inverse (A.adjoint H))) z =
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ F y w) (fderiv ℝ F y z)) x v +
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y z)) x w -
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w)) x z := by
  let A := fderiv ℝ F x
  let H := fun a b ↦ fderiv ℝ (fderiv ℝ F) x a b
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hprod (a b c : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ F y a) (fderiv ℝ F y b)) x c =
      inner ℝ (A a) (H c b) + inner ℝ (H c a) (A b) := by
    rw [fderiv_inner_apply ℝ (hDF.clm_apply (differentiableAt_const a))
      (hDF.clm_apply (differentiableAt_const b))]
    simp [fderiv_clm_apply hDF (differentiableAt_const a),
      fderiv_clm_apply hDF (differentiableAt_const b), A, H]
  have hs (a b : EuclideanSpace ℝ (Fin n)) : H a b = H b a :=
    hF.isSymmSndFDerivAt (by norm_num) a b
  have hi := hprod w z v
  have hj := hprod v z w
  have hk := hprod v w z
  rw [hs w v] at hj
  rw [hs z w, hs z v] at hk
  have hc := real_inner_comm (A w) (H v z)
  have hG := (frame_gram_positive_invertible A hA).2.2
  dsimp only
  rw [hG.self_apply_inverse]
  have ha := ContinuousLinearMap.adjoint_inner_left A z (H v w)
  change 2 * inner ℝ (A.adjoint (H v w)) z = _
  linarith

/-- The normal Hessian used above is the SAME actual trueSecondForm, evaluated
on the existing exact binary symmetric-square product in the identity chart.
Reuse accepted product evaluation and the native identity chart; no replacement
second form or quotient normalization is introduced. Source: true B in617–629. -/
theorem increments_trueSecondForm_coordinate {n N : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hF : ContDiff ℝ ∞ F) (x v w : EuclideanSpace ℝ (Fin n)) :
    (trueSecondForm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) F hF.contMDiff x
      (symmetricSquareProduct (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
        ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm v)
        ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm w)) :
      EuclideanSpace ℝ (Fin N)) =
      (LinearMap.range (fderiv ℝ F x).toLinearMap)ᗮ.starProjection
        (fderiv ℝ (fderiv ℝ F) x v w) := by
  rw [trueSecondForm_product]
  change (normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) F x).starProjection
    (fderiv ℝ (fderiv ℝ (F ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x x) v w) = _
  rw [extChartAt_model_space_eq_id]
  simp only [normalSpace, mfderiv_eq_fderiv]
  rfl

end GlobalEmbedding.Paper
