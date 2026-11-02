import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef

/-!
# The positive cone is open in the symmetric matrix space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, proof line 798. Positive metric roots are constructed by
local inverse calculus on the open cone of symmetric positive matrices. Continuity
of the actual quadratic pairing and compactness of the unit sphere give relative
openness, with no nonempty-index restriction.
-/

open scoped Topology Matrix.Norms.L2Operator

namespace GlobalEmbedding.Paper

open Matrix Filter

/-- Positive-definite real matrices form an open set in the native symmetric matrix
submodule. Every nonzero vector is a positive multiple of a unit vector, and the
unit sphere is compact. Joint continuity of the quadratic pairing therefore
preserves positivity for all unit vectors in a single parameter neighborhood.
Source: positive-root normalization in `prop:initialization`. -/
theorem isOpen_positive_symmetric_matrices
    {n : Type*} [Fintype n] [DecidableEq n] :
    IsOpen {A : selfAdjoint.submodule ℝ (Matrix n n ℝ) | (A : Matrix n n ℝ).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  let S := selfAdjoint.submodule ℝ (Matrix n n ℝ)
  let q : S → (n → ℝ) → ℝ := fun B v ↦ v ⬝ᵥ ((B : Matrix n n ℝ) *ᵥ v)
  have hq : Continuous (fun p : S × (n → ℝ) ↦ q p.1 p.2) := by
    have hcoe : Continuous (fun p : S × (n → ℝ) ↦ (p.1 : Matrix n n ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hvec (i : n) : Continuous (fun p : S × (n → ℝ) ↦ p.2 i) :=
      (continuous_apply i).comp continuous_snd
    dsimp [q, dotProduct, mulVec]
    apply continuous_finsetSum
    intro i hi
    apply Continuous.mul (hvec i)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp ((continuous_apply i).comp hcoe)).mul (hvec j)
  have hunit : ∀ᶠ B : S in 𝓝 A, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1, 0 < q B v := by
    apply (isCompact_sphere (0 : n → ℝ) 1).eventually_forall_of_forall_eventually
    intro v hv
    apply (isOpen_Ioi.preimage hq).mem_nhds
    change 0 < v ⬝ᵥ ((A : Matrix n n ℝ) *ᵥ v)
    have hv0 : v ≠ 0 := by
      intro hv0
      simp [hv0] at hv
    simpa only [star_trivial] using hA.dotProduct_mulVec_pos hv0
  filter_upwards [hunit] with B hB
  apply Matrix.PosDef.of_dotProduct_mulVec_pos B.property
  intro v hv
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : n → ℝ := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : n → ℝ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnv.ne']
  have hpos := hB w hw
  have heq : q B w = (‖v‖⁻¹ * ‖v‖⁻¹) * (v ⬝ᵥ ((B : Matrix n n ℝ) *ᵥ v)) := by
    simp only [q, w, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rw [heq] at hpos
  have hr : 0 < ‖v‖⁻¹ * ‖v‖⁻¹ := mul_pos (inv_pos.mpr hnv) (inv_pos.mpr hnv)
  simpa only [star_trivial] using (mul_pos_iff_of_pos_left hr).mp hpos

#print axioms isOpen_positive_symmetric_matrices

end GlobalEmbedding.Paper
