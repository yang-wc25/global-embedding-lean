import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The ideal first jet from the actual selector Gram identity

The linear map is the literal linear extension of the selector columns.  Its
isometry property is derived from `Matrix.gram = 1`.  A change of coframe then
produces the ideal first jet and its quantitative lower bound from the same
coefficient inverse.  These are preparation lemmas for `prop:initialization`;
they do not assert that the actual colored map has already been differentiated.
-/

noncomputable section

namespace GlobalEmbedding.Initialization

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The literal ideal frame map, with `D(e_i) = v_i`. -/
def gramFrame (v : Fin n → V) : EuclideanSpace ℝ (Fin n) →L[ℝ] V :=
  ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ v).toContinuousLinearMap

@[simp] theorem gramFrame_single (v : Fin n → V) (i : Fin n) :
    gramFrame v (EuclideanSpace.single i 1) = v i := by
  change (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ v
    (EuclideanSpace.single i 1) = v i
  simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using
    (Module.Basis.constr_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis ℝ v i)

/-- The ideal derivative is exactly the sum of its coefficient-weighted
selector columns, rather than an abstract isometry chosen independently. -/
theorem gramFrame_apply (v : Fin n → V) (u : EuclideanSpace ℝ (Fin n)) :
    gramFrame v u = ∑ i, u i • v i := by
  have hu := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u
  have h := congrArg (gramFrame v) hu
  simpa [map_sum, map_smul] using h.symm

theorem gramFrame_range (v : Fin n → V) :
    LinearMap.range (gramFrame v).toLinearMap = Submodule.span ℝ (Set.range v) :=
  Module.Basis.constr_range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis ℝ

theorem gramFrame_inner (v : Fin n → V) (hGram : Matrix.gram ℝ v = 1)
    (u w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (gramFrame v u) (gramFrame v w) = inner ℝ u w := by
  rw [gramFrame_apply, gramFrame_apply]
  have hv := Matrix.gram_eq_one_iff_orthonormal.mp hGram
  have h := hv.inner_sum (fun i ↦ u i) (fun i ↦ w i) Finset.univ
  simpa [PiLp.inner_apply, mul_comm] using h

@[simp] theorem gramFrame_norm (v : Fin n → V) (hGram : Matrix.gram ℝ v = 1)
    (u : EuclideanSpace ℝ (Fin n)) : ‖gramFrame v u‖ = ‖u‖ := by
  have h := gramFrame_inner v hGram u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The same frame becomes a linear isometry when its actual Gram is identity. -/
def gramFrameIsometry (v : Fin n → V) (hGram : Matrix.gram ℝ v = 1) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] V where
  toLinearMap := (gramFrame v).toLinearMap
  norm_map' := gramFrame_norm v hGram

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ideal first jet has the exact metric dictated by the coframe. -/
theorem idealFirstJet_norm (v : Fin n → V) (hGram : Matrix.gram ℝ v = 1)
    (c : E →L[ℝ] EuclideanSpace ℝ (Fin n)) (u : E) :
    ‖(gramFrame v).comp c u‖ = ‖c u‖ :=
  gramFrame_norm v hGram (c u)

/-- Uniform ellipticity follows from a genuine inverse bound on the coframe;
the harmless `1 + L` also covers a zero-dimensional domain. -/
theorem idealFirstJet_lower_bound (v : Fin n → V) (hGram : Matrix.gram ℝ v = 1)
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (L : ℝ)
    (hL : ‖c.symm.toContinuousLinearMap‖ ≤ L) (u : E) :
    (1 / (1 + L)) * ‖u‖ ≤ ‖(gramFrame v).comp c.toContinuousLinearMap u‖ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  have hden : 0 < 1 + L := by positivity
  rw [idealFirstJet_norm v hGram]
  have hu : ‖u‖ ≤ L * ‖c u‖ := by
    have hb := c.symm.toContinuousLinearMap.le_opNorm (c u)
    simpa using hb.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg (c u)))
  rw [one_div_mul_eq_div, div_le_iff₀ hden]
  change ‖u‖ ≤ ‖c u‖ * (1 + L)
  nlinarith [norm_nonneg (c u)]

end GlobalEmbedding.Initialization
