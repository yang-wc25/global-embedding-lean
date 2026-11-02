import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianTranslation

namespace GlobalEmbedding.Paper

/-- Every actual two-sided inverse of the original shifted Laplacian commutes with
actual torus translation. Reexpress the translated forcing as the Laplacian of the
translated solution, using the true L-translation identity and right inverse, and
apply the left inverse. Source: `literature/parallelizable-stable-plus-one/main.tex`,
`lem:balanced` proof, line 385. -/
theorem littlePeriodic_shiftedLaplacian_inverse_translate
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (f : LittlePeriodicCAlphaFunction a N 0 α) :
    W (littlePeriodicCAlphaTorusTranslate h f) =
      littlePeriodicCAlphaTorusTranslate h (W f) := by
  calc
    W (littlePeriodicCAlphaTorusTranslate h f) = W (littlePeriodicCAlphaShiftedLaplacian hα
        (littlePeriodicCAlphaTorusTranslate h (W f))) := by
      rw [littlePeriodic_shiftedLaplacian_translate, hLW]
    _ = littlePeriodicCAlphaTorusTranslate h (W f) := hWL _

#print axioms littlePeriodic_shiftedLaplacian_inverse_translate

end GlobalEmbedding.Paper
