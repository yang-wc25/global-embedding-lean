import GlobalEmbedding.Paper.PlanarProjectorSymbol
import GlobalEmbedding.Paper.PlanarHopfFlow
import GlobalEmbedding.External.SphereEversion.Local.DualPair

/-!
# The genuine initial reflection-equivariant Hopf map

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines 256–260.
The maps reduction uses the actual projective rank-one projector. Principal slices below
use the real upstream `DualPair.update`, rather than an independent slice operation.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The genuine provider principal derivative update has exactly the affine two-coordinate
symbol proved ample. All remaining terms are fixed in this principal slice. -/
theorem planarProjector_update_formula (z : E) (p : DualPair T)
    (φ : T →L[ℝ] ℝ × E) (X : T) (u : ℝ × E) (c : ℝ × ℝ) :
    planarProjectorSymbol z (p.update φ u X) + c =
      p.π X • planarProjectorSymbol z u +
        (planarProjectorSymbol z (φ X) - p.π X • planarProjectorSymbol z (φ p.v) + c) := by
  simp only [DualPair.update, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, map_add, map_smul, map_sub, smul_sub]
  abel

/-- Actual principal slices, formed with the actual imported `DualPair.update`, are ample.
The covector coefficient may vanish; no nontrivial-slice condition is added as a hypothesis. -/
theorem planarProjector_update_ample [FiniteDimensional ℝ E]
    (z : E) (hz : ‖z‖ = 1) (p : DualPair T) (φ : T →L[ℝ] ℝ × E)
    (X : T) (c : ℝ × ℝ) :
    AmpleSet {u : ℝ × E | planarProjectorSymbol z (p.update φ u X) + c ≠ 0} := by
  have heq : {u : ℝ × E | planarProjectorSymbol z (p.update φ u X) + c ≠ 0} =
      {u : ℝ × E | p.π X • planarProjectorSymbol z u +
        (planarProjectorSymbol z (φ X) - p.π X • planarProjectorSymbol z (φ p.v) + c) ≠ 0} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    rw [planarProjector_update_formula]
  rw [heq]
  exact planarProjectorSymbol_affine_ample z hz _ _

/-- The original ambient-projector nonvanishing condition in an actual principal slice is
ample. The displayed projector identities are pointwise algebraic inputs here, to be supplied
by the true native projective projector in the final existence construction. -/
theorem planarProjector_native_slice_ample [FiniteDimensional ℝ E]
    (z v w : E) (hz : ‖z‖ = 1) (hv : ⟪z, v⟫ = 0)
    (P dP : E →L[ℝ] E) (hP : ∀ y, P y = ⟪z, y⟫ • z)
    (hdP : ∀ y, dP y = ⟪z, y⟫ • v + ⟪v, y⟫ • z)
    (p : DualPair T) (φ : T →L[ℝ] ℝ × E) (X : T) :
    AmpleSet {u : ℝ × E |
      ((p.update φ u X).1, P (p.update φ u X).2 + P (dP w)) ≠ (0 : ℝ × E)} := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have heq : {u : ℝ × E |
      ((p.update φ u X).1, P (p.update φ u X).2 + P (dP w)) ≠ (0 : ℝ × E)} =
      {u : ℝ × E | planarProjectorSymbol z (p.update φ u X) + (0, ⟪w, v⟫) ≠ 0} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    rw [planarProjector_lift_identity z v w (p.update φ u X).2 hz hv P dP hP hdP]
    simp [planarProjectorSymbol_apply, smul_eq_zero, hz0]
  rw [heq]
  exact planarProjector_update_ample z hz p φ X _

#print axioms planarProjector_update_formula
#print axioms planarProjector_update_ample
#print axioms planarProjector_native_slice_ample

end GlobalEmbedding.Paper
