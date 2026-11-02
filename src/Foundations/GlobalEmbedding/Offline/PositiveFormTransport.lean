import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Module LinearMap QuadraticMap
open scoped BigOperators

/-!
# Native transport of positive definite real forms

Native quadratic-form orthogonal bases and positive square roots give an actual linear
isometry between any two positive definite symmetric real bilinear forms of equal finite
dimension.  No chosen isometry is assumed, and no topology or analytic norm is changed.
This is the metric transport step used by the positive rank-one dictionary construction.
-/

namespace GlobalEmbedding.Offline

theorem positive_quadratic_isometry_sum_squares
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    Nonempty (Q.IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ (fun _ : Fin (Module.finrank ℝ V) ↦ (1 : ℝ)))) := by
  classical
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := QuadraticMap.associated (R := ℝ) Q) ⟨associated_isSymm ℝ Q⟩
  let e := Q.isometryEquivWeightedSumSquares b hb
  have hpos (i : Fin (Module.finrank ℝ V)) : 0 < Q (b i) := hQ _ (b.ne_zero i)
  let u : Fin (Module.finrank ℝ V) → ℝˣ := fun i ↦
    Units.mk0 (Real.sqrt (Q (b i))) (Real.sqrt_pos.mpr (hpos i)).ne'
  have hu (i : Fin (Module.finrank ℝ V)) : (1 : ℝ) * (u i : ℝ) ^ 2 = Q (b i) := by
    simp only [u, Units.val_mk0, one_mul, Real.sq_sqrt (hpos i).le]
  exact ⟨e.trans (QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares u hu)⟩

theorem positive_quadratic_isometry_of_finrank_eq
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (Q : QuadraticForm ℝ V) (P : QuadraticForm ℝ W)
    (hQ : Q.PosDef) (hP : P.PosDef) (hdim : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Q.IsometryEquiv P) := by
  obtain ⟨eQ⟩ := positive_quadratic_isometry_sum_squares Q hQ
  have hP' : Nonempty (P.IsometryEquiv
      (QuadraticMap.weightedSumSquares ℝ (fun _ : Fin (Module.finrank ℝ V) ↦ (1 : ℝ)))) := by
    exact hdim.symm ▸ positive_quadratic_isometry_sum_squares P hP
  obtain ⟨eP⟩ := hP'
  exact ⟨eQ.trans eP.symm⟩

theorem positive_bilinear_isometry_of_finrank_eq
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (hB : B.IsSymm) (hC : C.IsSymm)
    (hBpos : ∀ x, x ≠ 0 → 0 < B x x) (hCpos : ∀ x, x ≠ 0 → 0 < C x x)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W) :
    ∃ e : V ≃ₗ[ℝ] W, ∀ x y, C (e x) (e y) = B x y := by
  obtain ⟨e⟩ := positive_quadratic_isometry_of_finrank_eq
    B.toQuadraticMap C.toQuadraticMap hBpos hCpos hdim
  have heq : B = C.comp e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap := by
    apply LinearMap.BilinForm.ext_of_isSymm hB ⟨fun x y ↦ hC.eq _ _⟩
    intro x
    exact (e.map_app x).symm
  refine ⟨e.toLinearEquiv, fun x y ↦ ?_⟩
  exact (congrArg (fun A : LinearMap.BilinForm ℝ V ↦ A x y) heq).symm

#print axioms positive_quadratic_isometry_sum_squares
#print axioms positive_quadratic_isometry_of_finrank_eq
#print axioms positive_bilinear_isometry_of_finrank_eq

end GlobalEmbedding.Offline
