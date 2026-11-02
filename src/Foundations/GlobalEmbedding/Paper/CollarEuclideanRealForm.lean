import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

/-!
# The canonical actual real form of finite complex Euclidean parameter space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. All source coefficient families use this same actual parameter submodule.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual real parameter submodule consists of complex Euclidean vectors with zero
coordinatewise imaginary part. Its operations are the inherited actual real operations.
Source: Proposition `prop:collar`, real base/translation parameters. -/
def collarEuclideanRealSubmodule (d : ℕ) : Submodule ℝ (EuclideanSpace ℂ (Fin d)) where
  carrier := {z | ∀ i, (z i).im = 0}
  zero_mem' := by intro i; rfl
  add_mem' := by
    intro x y hx hy i
    change (x i + y i).im = 0
    rw [Complex.add_im, hx i, hy i, add_zero]
  smul_mem' := by
    intro c x hx i
    change Complex.imCLM (c • x i) = 0
    rw [map_smul]
    change c * (x i).im = 0
    rw [hx i, mul_zero]

/-- The canonical real Euclidean coordinate inclusion is an actual linear isometry onto the
canonical real submodule. Its inverse is actual coordinatewise real part.
Source: Proposition `prop:collar`, real parameter form. The two inverse laws follow by real and
imaginary coordinates; equality of Euclidean norms follows by the coordinate norm squares.
This includes d=0. No norm equivalence constant or real-form existence is assumed. -/
noncomputable def collarEuclideanRealEquiv (d : ℕ) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] collarEuclideanRealSubmodule d where
  toLinearEquiv :=
    { toFun := fun x ↦ ⟨toLp 2 (fun i ↦ (x i : ℂ)), fun _ ↦ Complex.ofReal_im _⟩
      invFun := fun z ↦ toLp 2 (fun i ↦ (z.val i).re)
      left_inv := by intro x; ext i; rfl
      right_inv := by
        intro z
        apply Subtype.ext
        ext i
        apply Complex.ext
        · rfl
        · exact (z.property i).symm
      map_add' := by intro x y; apply Subtype.ext; ext i; simp
      map_smul' := by intro c x; apply Subtype.ext; ext i; simp }
  norm_map' := by
    intro x
    change ‖(toLp 2 (fun i ↦ (x i : ℂ)) : EuclideanSpace ℂ (Fin d))‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑ i : Fin d, ‖(x i : ℂ)‖ ^ 2) = ∑ i : Fin d, ‖x i‖ ^ 2
    simp only [Complex.norm_real]

/-- The canonical real parameter submodule is actually closed.
Source: Proposition `prop:collar`, real parameters. It is the intersection of the zero sets
of the continuous coordinate imaginary-part maps. -/
theorem collar_euclidean_real_submodule_closed (d : ℕ) :
    IsClosed (collarEuclideanRealSubmodule d : Set (EuclideanSpace ℂ (Fin d))) := by
  change IsClosed {z : EuclideanSpace ℂ (Fin d) | ∀ i, (z i).im = 0}
  have he : {z : EuclideanSpace ℂ (Fin d) | ∀ i, (z i).im = 0} =
      ⋂ i : Fin d, {z : EuclideanSpace ℂ (Fin d) | (z i).im = 0} := by ext z; simp
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_eq
    (Complex.continuous_im.comp (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℂ) i)) continuous_const

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarEuclideanRealSubmodule
#print axioms GlobalEmbedding.Paper.collarEuclideanRealEquiv
#print axioms GlobalEmbedding.Paper.collar_euclidean_real_submodule_closed
