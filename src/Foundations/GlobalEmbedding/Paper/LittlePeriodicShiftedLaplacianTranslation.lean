import GlobalEmbedding.Paper.LittlePeriodicCAlphaShiftedLaplacianLift
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLift

/-!
# The actual shifted Laplacian commutes with actual torus translations

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced` proof.
DAG node: `balanced-inverse-periodic-laplacian-translation`.
-/

namespace GlobalEmbedding.Paper

/-- The original shifted Laplacian commutes with every actual torus translation.
Choose a Euclidean representative and use the every-lift formula. The actual twice
Frechet-differentiated translation is the translation of the actual second derivative,
by `fderiv_comp_add_right` twice. The exact original Laplacian lift and injectivity of
original function data prove equality in the actual little spaces.
Source: translation invariance in the proof of `lem:balanced`. -/
theorem littlePeriodic_shiftedLaplacian_translate {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (u : LittlePeriodicCAlphaFunction a N 2 α) :
    littlePeriodicCAlphaShiftedLaplacian hα (littlePeriodicCAlphaTorusTranslate h u) =
      littlePeriodicCAlphaTorusTranslate h (littlePeriodicCAlphaShiftedLaplacian hα u) := by
  obtain ⟨v, rfl⟩ := periodic_flat_torus_projection.surjective h
  rw [littlePeriodicCAlphaTorusTranslate_lift, littlePeriodicCAlphaTorusTranslate_lift]
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  rw [littlePeriodicCAlphaShiftedLaplacian_lift]
  change (∑ i : Fin a, fderiv ℝ
    (fun y ↦ fderiv ℝ (fun z ↦ u.val.toFun (z + v)) y
      (EuclideanSpace.basisFun (Fin a) ℝ i)) x
      (EuclideanSpace.basisFun (Fin a) ℝ i)) - u.val.toFun (x + v) =
    (littlePeriodicCAlphaShiftedLaplacian hα u).val.toFun (x + v)
  simp_rw [fderiv_comp_add_right]
  rw [littlePeriodicCAlphaShiftedLaplacian_lift]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun A ↦ A (EuclideanSpace.basisFun (Fin a) ℝ i))
    (fderiv_comp_add_right (𝕜 := ℝ)
      (f := fun y ↦ fderiv ℝ u.val.toFun y (EuclideanSpace.basisFun (Fin a) ℝ i))
      (x := x) v)

#print axioms littlePeriodic_shiftedLaplacian_translate

end GlobalEmbedding.Paper
