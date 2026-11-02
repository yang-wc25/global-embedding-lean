import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ContDiff Laplacian

namespace GlobalEmbedding.Paper

/-- The genuine Euclidean Laplacian is exactly the original repeated coordinate
Frechet derivative sum. Use the actual orthonormal trace identity, and differentiate
the evaluation of the genuine first derivative at a constant basis vector. No chosen
formal second-derivative field occurs. Empty source and zero targets are included. -/
theorem euclidean_laplacian_eq_coordinate_second
    {a : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : EuclideanSpace ℝ (Fin a) → F) (hu : ContDiff ℝ 2 u)
    (x : EuclideanSpace ℝ (Fin a)) :
    Laplacian.laplacian u x = ∑ i : Fin a, fderiv ℝ
      (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin a) ℝ i)) x
      (EuclideanSpace.basisFun (Fin a) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin a) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const (EuclideanSpace.basisFun (Fin a) ℝ i))]
  simp [iteratedFDeriv_two_apply]

#print axioms euclidean_laplacian_eq_coordinate_second

end GlobalEmbedding.Paper
