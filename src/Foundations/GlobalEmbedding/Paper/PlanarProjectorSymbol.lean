import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Prod

/-!
# The projector symbol for the initial equivariant planar map

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines 256–260.
The initial-map construction uses the rank-one real projector on real projective space.
These are the pointwise algebraic steps of that construction, before its native jet relation
and the actual maps h-principle are instantiated. No initial map or solution is assumed here.
-/

noncomputable section

open scoped RealInnerProductSpace
open scoped Pointwise

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two actual free derivative coordinates at a unit representative of a projective line. -/
def planarProjectorSymbol (z : E) : (ℝ × E) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ E).prod
    ((innerSL ℝ z).comp (ContinuousLinearMap.snd ℝ ℝ E))

@[simp] theorem planarProjectorSymbol_apply (z : E) (u : ℝ × E) :
    planarProjectorSymbol z u = (u.1, ⟪z, u.2⟫) := rfl

/-- The projector slice has two genuinely independent free coordinates, not an assumed rank.
The preimage of `(a,b)` is explicitly `(a,b • z)` for a unit vector `z`. -/
theorem planarProjectorSymbol_surjective (z : E) (hz : ‖z‖ = 1) :
    Function.Surjective (planarProjectorSymbol z) := by
  rintro ⟨a, b⟩
  refine ⟨(a, b • z), ?_⟩
  simp [real_inner_smul_right, hz]

/-- The forbidden linear fiber has actual codimension two. This uses the first isomorphism
theorem on the explicitly surjective two-coordinate symbol. -/
theorem planarProjectorSymbol_codimension [FiniteDimensional ℝ E]
    (z : E) (hz : ‖z‖ = 1) :
    Module.finrank ℝ ((ℝ × E) ⧸ (planarProjectorSymbol z).toLinearMap.ker) = 2 := by
  let e := (planarProjectorSymbol z).toLinearMap.quotKerEquivOfSurjective
    (planarProjectorSymbol_surjective z hz)
  calc
    _ = Module.finrank ℝ (ℝ × ℝ) := e.finrank_eq
    _ = 2 := by simp

/-- In a principal slice through a projective unit representative the complement of the
forbidden linear fiber is ample, by its proved codimension two. -/
theorem planarProjectorSymbol_ample [FiniteDimensional ℝ E] (z : E) (hz : ‖z‖ = 1) :
    AmpleSet (((planarProjectorSymbol z).toLinearMap.ker : Set (ℝ × E))ᶜ) := by
  apply AmpleSet.of_one_lt_codim
  rw [← Module.finrank_eq_rank, planarProjectorSymbol_codimension z hz]
  norm_num

/-- The actual affine principal-slice condition is ample, including the slices whose
free covector annihilates the Hopf field. Its forbidden fiber is a translate of the
proved codimension-two kernel; when the coefficient is zero the slice is empty or full. -/
theorem planarProjectorSymbol_affine_ample [FiniteDimensional ℝ E]
    (z : E) (hz : ‖z‖ = 1) (α : ℝ) (c : ℝ × ℝ) :
    AmpleSet {u : ℝ × E | α • planarProjectorSymbol z u + c ≠ 0} := by
  by_cases hα : α = 0
  · by_cases hc : c = 0 <;> simp [hα, hc]
  obtain ⟨b, hb⟩ := planarProjectorSymbol_surjective z hz (-α⁻¹ • c)
  have hb' : α • planarProjectorSymbol z b = -c := by
    rw [hb, smul_smul, mul_neg, mul_inv_cancel₀ hα, neg_one_smul]
  have heq : {u : ℝ × E | α • planarProjectorSymbol z u + c ≠ 0} =
      b +ᵥ (((planarProjectorSymbol z).toLinearMap.ker : Set (ℝ × E))ᶜ) := by
    ext u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (α • planarProjectorSymbol z u + c ≠ 0) ↔
      planarProjectorSymbol z (-b + u) ≠ 0
    have hshift : α • planarProjectorSymbol z (-b + u) =
        α • planarProjectorSymbol z u + c := by
      rw [map_add, map_neg, smul_add, smul_neg, hb', neg_neg, add_comm]
    rw [← hshift, ne_eq, smul_eq_zero]
    simp [hα]
  rw [heq]
  exact (planarProjectorSymbol_ample z hz).vadd

/-- Differentiating the actual rank-one projector gives precisely the lifted scalar derivative.
The tangent vector is orthogonal to the unit representative, as on the actual sphere. -/
theorem planarProjector_lift_identity (z v w u : E) (hz : ‖z‖ = 1)
    (hv : ⟪z, v⟫ = 0) (P dP : E →L[ℝ] E)
    (hP : ∀ y, P y = ⟪z, y⟫ • z)
    (hdP : ∀ y, dP y = ⟪z, y⟫ • v + ⟪v, y⟫ • z) :
    P u + P (dP w) = (⟪z, u⟫ + ⟪w, v⟫) • z := by
  rw [hP, hP, hdP]
  simp only [inner_add_right, real_inner_smul_right, hv, mul_zero,
    real_inner_self_eq_norm_sq, hz, one_pow, mul_one, zero_add]
  rw [real_inner_comm v w, add_smul]

/-- A nonzero ambient-projector pair really gives a nonzero lifted planar derivative.
This is the exact pointwise bridge needed after constructing the genuine projective map. -/
theorem planarProjector_lift_nonzero (z v w u : E) (a : ℝ) (hz : ‖z‖ = 1)
    (hv : ⟪z, v⟫ = 0) (P dP : E →L[ℝ] E)
    (hP : ∀ y, P y = ⟪z, y⟫ • z)
    (hdP : ∀ y, dP y = ⟪z, y⟫ • v + ⟪v, y⟫ • z)
    (h : (a, P u + P (dP w)) ≠ (0 : ℝ × E)) :
    (a, ⟪z, u⟫ + ⟪w, v⟫) ≠ (0 : ℝ × ℝ) := by
  rw [planarProjector_lift_identity z v w u hz hv P dP hP hdP] at h
  intro hzero
  have ha : a = 0 := congrArg Prod.fst hzero
  have hb : ⟪z, u⟫ + ⟪w, v⟫ = 0 := congrArg Prod.snd hzero
  apply h
  simp [ha, hb]

#print axioms planarProjectorSymbol_surjective
#print axioms planarProjectorSymbol_codimension
#print axioms planarProjectorSymbol_ample
#print axioms planarProjectorSymbol_affine_ample
#print axioms planarProjector_lift_identity
#print axioms planarProjector_lift_nonzero

end GlobalEmbedding.Paper
