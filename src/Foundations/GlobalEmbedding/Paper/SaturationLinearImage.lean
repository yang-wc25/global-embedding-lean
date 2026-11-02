import GlobalEmbedding.Paper.SaturationPolynomialImage
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual linear parameter families and polynomial image propagation

Source: original `prop:saturation`, lines971–985. The linear entries of the actual
family are encoded using the native coordinate basis. Actual column injectivity
discharges Gram nonsingularity by the native Gram-kernel identity. No extra global
image relation or desired saturation identity is an input.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {σ I J : Type*} [Fintype σ] [DecidableEq σ]

/-- The literal linear polynomial of an actual real coordinate functional.
Source: the actual covector-coordinate entries in the original cone identity. -/
def saturationLinearPolynomial (f : (σ → ℝ) →ₗ[ℝ] ℝ) : MvPolynomial σ ℝ :=
  ∑ k, MvPolynomial.C (f (Pi.single k 1)) * MvPolynomial.X k

/-- Evaluation recovers the original functional, using native basis reconstruction.
Source: the original cone identity, with no replacement coordinate function. -/
theorem saturationLinearPolynomial_eval (f : (σ → ℝ) →ₗ[ℝ] ℝ) (x : σ → ℝ) :
    MvPolynomial.eval x (saturationLinearPolynomial f) = f x := by
  simp only [saturationLinearPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  have h := congrArg f ((Pi.basisFun ℝ σ).sum_repr x)
  simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply,
    smul_eq_mul, mul_comm] using h

/-- The actual real Gram determinant is nonzero when the column map is injective.
Source: the good-evaluation condition in the original saturation proof. -/
theorem saturation_gram_det_ne_zero [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℝ) (hA : Function.Injective A.mulVec) :
    (A.transpose * A).det ≠ 0 := by
  have hi : Function.Injective (A.transpose * A).mulVec := by
    change Function.Injective (A.transpose * A).mulVecLin
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hA
  have hu := Matrix.mulVec_injective_iff_isUnit.mp hi
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

/-- One actual injective evaluation ensures another in every nonempty open set.
This is the nonzero Gram polynomial, not a supplied density assumption.
Source: original `prop:saturation`, global maximal evaluation rank. -/
theorem saturation_linear_injective_meets_open
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : (σ → ℝ) →ₗ[ℝ] Matrix I J ℝ)
    (hinj : ∃ x, Function.Injective (A x).mulVec)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, Function.Injective (A x).mulVec := by
  let Ap : Matrix I J (MvPolynomial σ ℝ) := fun i j ↦
    saturationLinearPolynomial ((LinearMap.proj j).comp ((LinearMap.proj i).comp A))
  have hA (x : σ → ℝ) : Ap.map (MvPolynomial.eval x) = A x := by
    ext i j
    exact saturationLinearPolynomial_eval _ x
  have hg (x : σ → ℝ) : MvPolynomial.eval x (Ap.transpose * Ap).det =
      ((A x).transpose * A x).det := by
    rw [RingHom.map_det]
    congr 1
    change (Ap.transpose * Ap).map (MvPolynomial.eval x) = _
    rw [Matrix.map_mul]
    change (Ap.map (MvPolynomial.eval x)).transpose * Ap.map (MvPolynomial.eval x) = _
    rw [hA]
  have hp : (Ap.transpose * Ap).det ≠ 0 := by
    obtain ⟨x, hx⟩ := hinj
    intro hz
    have hd := saturation_gram_det_ne_zero (A x) hx
    rw [← hg x, hz, map_zero] at hd
    exact hd rfl
  obtain ⟨x, hx, hd⟩ := saturation_polynomial_exists_ne_zero_on_open
    (Ap.transpose * Ap).det hp U hU hne
  rw [hg] at hd
  have hu : IsUnit ((A x).transpose * A x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hu
  refine ⟨x, hx, ?_⟩
  change Function.Injective (A x).mulVecLin
  rw [← LinearMap.ker_eq_bot, ← Matrix.ker_mulVecLin_transpose_mul_self]
  exact LinearMap.ker_eq_bot.mpr hi

/-- Actual linear matrix/vector families satisfy the same image relation at every
point where the actual matrix is injective. The initial open set need not consist
of injective points. All zero-dimensional coordinate cases remain valid.
Source: original `prop:saturation`, cone-to-all-good propagation. -/
theorem saturation_linear_image_of_open
    [Fintype I] [Fintype J] [DecidableEq J]
    (A : (σ → ℝ) →ₗ[ℝ] Matrix I J ℝ)
    (b : (σ → ℝ) →ₗ[ℝ] (I → ℝ))
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, ∃ v : J → ℝ, (A x).mulVec v = b x) :
    ∀ x : σ → ℝ, Function.Injective (A x).mulVec →
      ∃ v : J → ℝ, (A x).mulVec v = b x := by
  let Ap : Matrix I J (MvPolynomial σ ℝ) := fun i j ↦
    saturationLinearPolynomial ((LinearMap.proj j).comp ((LinearMap.proj i).comp A))
  let bp : I → MvPolynomial σ ℝ := fun i ↦
    saturationLinearPolynomial ((LinearMap.proj i).comp b)
  have hA (x : σ → ℝ) : Ap.map (MvPolynomial.eval x) = A x := by
    ext i j
    exact saturationLinearPolynomial_eval _ x
  have hb (x : σ → ℝ) : (fun i ↦ MvPolynomial.eval x (bp i)) = b x := by
    funext i
    exact saturationLinearPolynomial_eval _ x
  have hp := saturation_polynomial_image_of_open Ap bp U hU hne
    (fun x hx ↦ by simpa only [hA, hb] using h x hx)
  intro x hx
  have hg : (MvPolynomial.eval x).mapMatrix (Ap.transpose * Ap) =
      (A x).transpose * A x := by
    change (Ap.transpose * Ap).map (MvPolynomial.eval x) = _
    rw [Matrix.map_mul]
    change (Ap.map (MvPolynomial.eval x)).transpose * Ap.map (MvPolynomial.eval x) = _
    rw [hA]
  have hd : MvPolynomial.eval x (Ap.transpose * Ap).det ≠ 0 := by
    rw [RingHom.map_det, hg]
    exact saturation_gram_det_ne_zero (A x) hx
  simpa only [hA, hb] using hp x hd

/-- The same propagation in arbitrary finite-dimensional real parameter, source and
value spaces. Only the parameter space needs a topology. Native basis coordinates
are used internally, without any inner product or extra coordinate hypothesis.
Source: original `prop:saturation`, the actual covector-parameter application. -/
theorem saturation_linear_family_image_of_open
    {D K V : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [AddCommGroup K] [Module ℝ K] [FiniteDimensional ℝ K]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (A : D →ₗ[ℝ] K →ₗ[ℝ] V) (b : D →ₗ[ℝ] V)
    (U : Set D) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, ∃ v : K, A x v = b x) :
    ∀ x : D, Function.Injective (A x) → ∃ v : K, A x v = b x := by
  let db := Module.finBasis ℝ D
  let kb := Module.finBasis ℝ K
  let vb := Module.finBasis ℝ V
  let e := db.equivFunL
  let Ac := ((LinearMap.toMatrix kb vb).toLinearMap.comp A).comp e.symm.toLinearMap
  let bc := (vb.equivFun.toLinearMap.comp b).comp e.symm.toLinearMap
  have hm (x : Fin (Module.finrank ℝ D) → ℝ) (v : K) :
      (Ac x).mulVec (kb.equivFun v) = vb.equivFun (A (e.symm x) v) := by
    change (LinearMap.toMatrix kb vb (A (e.symm x))).mulVec (kb.equivFun v) = _
    simpa only [Module.Basis.equivFun_apply] using
      (A (e.symm x)).toMatrix_mulVec_repr kb vb v
  have hc : ∀ x ∈ e.symm ⁻¹' U,
      ∃ v, (Ac x).mulVec v = bc x := by
    intro x hx
    obtain ⟨v, hv⟩ := h (e.symm x) hx
    refine ⟨kb.equivFun v, ?_⟩
    rw [hm, hv]
    rfl
  have hn : (e.symm ⁻¹' U).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, by simpa only [Set.mem_preimage, e.symm_apply_apply] using hx⟩
  have hp := saturation_linear_image_of_open Ac bc (e.symm ⁻¹' U)
    (hU.preimage e.symm.continuous) hn hc
  intro x hx
  have hi : Function.Injective (Ac (e x)).mulVec := by
    intro u v huv
    apply kb.equivFun.symm.injective
    apply hx
    apply vb.equivFun.injective
    have hu := hm (e x) (kb.equivFun.symm u)
    have hv := hm (e x) (kb.equivFun.symm v)
    simp only [e.symm_apply_apply, kb.equivFun.apply_symm_apply] at hu hv
    exact hu.symm.trans (huv.trans hv)
  obtain ⟨v, hv⟩ := hp (e x) hi
  refine ⟨kb.equivFun.symm v, ?_⟩
  apply vb.equivFun.injective
  have hh := hm (e x) (kb.equivFun.symm v)
  change (Ac (e x)).mulVec v = vb.equivFun (b (e.symm (e x))) at hv
  simp only [e.symm_apply_apply, kb.equivFun.apply_symm_apply] at hh hv
  exact hh.symm.trans hv

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturationLinearPolynomial
#print axioms GlobalEmbedding.Paper.saturationLinearPolynomial_eval
#print axioms GlobalEmbedding.Paper.saturation_gram_det_ne_zero
#print axioms GlobalEmbedding.Paper.saturation_linear_injective_meets_open
#print axioms GlobalEmbedding.Paper.saturation_linear_image_of_open
#print axioms GlobalEmbedding.Paper.saturation_linear_family_image_of_open
