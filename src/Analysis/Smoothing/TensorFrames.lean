import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Basic.Real.Basic

/-!
# Genuine bilinear tensor coordinates and changes of frame

Source: `main.tex`, the tensor part of (6.4), and the ordered native tensor
components in `IncrementsOriginalNativeCoordinates`. This module uses actual
bilinear forms and actual bases. Reconstruction is inverse to taking ALL
ordered components. Different frames are related by the full `Jᵀ H J`
formula; no coordinate-independent component smoothing is asserted.
-/

open Matrix Module
open scoped BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The exact ordered component vector, flattened by the same equivalence
as `incrementsOriginalTensorCoordinates`. -/
def tensorFrameComponents (b : Basis (Fin n) ℝ V)
    (H : LinearMap.BilinForm ℝ V) : Fin (n * n) → ℝ :=
  fun k => H (b (finProdFinEquiv.symm k).1) (b (finProdFinEquiv.symm k).2)

/-- Reconstruct an actual bilinear form from all its ordered components. -/
def tensorFromFrameComponents (b : Basis (Fin n) ℝ V)
    (u : Fin (n * n) → ℝ) : LinearMap.BilinForm ℝ V :=
  Matrix.toBilin b (fun i j => u (finProdFinEquiv (i, j)))

@[simp]
theorem tensorFromFrameComponents_components (b : Basis (Fin n) ℝ V)
    (H : LinearMap.BilinForm ℝ V) :
    tensorFromFrameComponents b (tensorFrameComponents b H) = H := by
  unfold tensorFromFrameComponents tensorFrameComponents
  simp only [Equiv.symm_apply_apply]
  have hm : (fun i j => H (b i) (b j)) = H.toMatrix b := by
    ext i j
    exact (LinearMap.BilinForm.toMatrix_apply b H i j).symm
  rw [hm]
  exact Matrix.toBilin_toMatrix b H

@[simp]
theorem tensorFrameComponents_fromComponents (b : Basis (Fin n) ℝ V)
    (u : Fin (n * n) → ℝ) :
    tensorFrameComponents b (tensorFromFrameComponents b u) = u := by
  funext k
  have h := congrFun (congrFun
    (LinearMap.BilinForm.toMatrix_toBilin b (fun i j => u (finProdFinEquiv (i, j))))
    (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
  simpa only [tensorFrameComponents, tensorFromFrameComponents,
    LinearMap.BilinForm.toMatrix_apply, Prod.mk.eta, Equiv.apply_symm_apply] using h

/-- Componentwise equality determines the actual tensor, including dimension zero. -/
theorem tensorFrameComponents_injective (b : Basis (Fin n) ℝ V) :
    Function.Injective (tensorFrameComponents b) := by
  intro H K h
  have := congrArg (tensorFromFrameComponents b) h
  simpa only [tensorFromFrameComponents_components] using this

@[simp]
theorem tensorFrameComponents_sub (b : Basis (Fin n) ℝ V)
    (H K : LinearMap.BilinForm ℝ V) :
    tensorFrameComponents b (H - K) = tensorFrameComponents b H - tensorFrameComponents b K := rfl

@[simp]
theorem tensorFromFrameComponents_sub (b : Basis (Fin n) ℝ V)
    (u v : Fin (n * n) → ℝ) :
    tensorFromFrameComponents b (u - v) =
      tensorFromFrameComponents b u - tensorFromFrameComponents b v := by
  unfold tensorFromFrameComponents
  exact map_sub (Matrix.toBilin b) _ _

@[simp]
theorem tensorFromFrameComponents_smul (b : Basis (Fin n) ℝ V)
    (c : ℝ) (u : Fin (n * n) → ℝ) :
    tensorFromFrameComponents b (c • u) = c • tensorFromFrameComponents b u := by
  unfold tensorFromFrameComponents
  exact map_smul (Matrix.toBilin b) _ _

/-- Symmetry is retained by genuine reconstruction. No positivity follows
from this statement, since the smoothing kernels may have either sign. -/
theorem tensorFromFrameComponents_isSymm (b : Basis (Fin n) ℝ V)
    (u : Fin (n * n) → ℝ)
    (hu : ∀ i j, u (finProdFinEquiv (i, j)) = u (finProdFinEquiv (j, i))) :
    (tensorFromFrameComponents b u).IsSymm := by
  apply (Matrix.isSymm_toBilin_iff_isSymm b).mpr
  ext i j
  exact (hu i j).symm

/-- The FULL ordered-coordinate change: each output slot is a double
contraction with the genuine basis-change matrix. -/
theorem tensorFrameComponents_change (b c : Basis (Fin n) ℝ V)
    (H : LinearMap.BilinForm ℝ V) (i j : Fin n) :
    tensorFrameComponents c H (finProdFinEquiv (i, j)) =
      ∑ a, ∑ d, b.repr (c i) a *
        tensorFrameComponents b H (finProdFinEquiv (a, d)) * b.repr (c j) d := by
  simp only [tensorFrameComponents, Equiv.symm_apply_apply]
  conv_lhs => rw [← Matrix.toBilin_toMatrix b H]
  rw [Matrix.toBilin_apply]
  simp only [LinearMap.BilinForm.toMatrix_apply]

/-- The coordinate transformation is precisely `Jᵀ H J`, not a relabelling. -/
theorem tensor_matrix_change (b c : Basis (Fin n) ℝ V)
    (H : LinearMap.BilinForm ℝ V) :
    H.toMatrix c = (b.toMatrix c)ᵀ * H.toMatrix b * b.toMatrix c :=
  (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c H).symm

end

end GlobalEmbedding.Offline
