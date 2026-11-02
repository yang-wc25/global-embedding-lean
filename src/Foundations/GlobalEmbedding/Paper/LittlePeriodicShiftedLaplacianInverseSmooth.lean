import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianInverseTranslation
import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianSmoothSurjectivity
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslationIntertwinerWord

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual left inverse preserves genuine smooth periodic lifts. The actual smooth
periodic PDE construction gives a genuine smooth little2 solution; applying the left
inverse identifies it with Wf. No regularity of W is assumed.
Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line385. -/
theorem littlePeriodic_shiftedLaplacian_inverse_smooth
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun) :
    ContDiff ℝ ∞ (W f).val.toFun := by
  obtain ⟨u, hu, hLu⟩ := littlePeriodic_shiftedLaplacian_smooth_surjectivity hα f hf
  have he : W f = u := by rw [← hLu]; exact hWL u
  rw [he]
  exact hu

/-- The actual inverse commutes with arbitrary actual directional differentiation on
smooth lifts. Smooth upgrade gives the genuine one-order-higher representatives needed
by the norm-level translation-derivative theorem. Actual inverse translation and genuine
smooth preservation discharge its hypotheses. Exact lifts identify the prescribed
forcing derivative. Source: all derivatives in the proof of `lem:balanced`,
`literature/parallelizable-stable-plus-one/main.tex`. -/
theorem littlePeriodic_shiftedLaplacian_inverse_directional
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (v : EuclideanSpace ℝ (Fin a)) (g : LittlePeriodicCAlphaFunction a N 0 α)
    (hg : g.val.toFun = fun x ↦ fderiv ℝ f.val.toFun x v) :
    (W g).val.toFun = fun x ↦ fderiv ℝ (W f).val.toFun x v := by
  obtain ⟨f', hf'⟩ := periodicCAlpha_smooth_upgrade f.val hf hα 1
  obtain ⟨u', hu'⟩ := periodicCAlpha_smooth_upgrade (W f).val
    (littlePeriodic_shiftedLaplacian_inverse_smooth hα W hWL f hf) hα 3
  have hD := littlePeriodicCAlpha_translation_intertwiner_derivative hα W
    (littlePeriodic_shiftedLaplacian_inverse_translate hα W hWL hLW) f' f hf' u' hu' v
  have hfg : littlePeriodicCAlphaDirectionalDerivative v f' = g := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    change fderiv ℝ f'.val.toFun x v = g.val.toFun x
    rw [hf', hg]
  funext x
  rw [← hfg, hD]
  change fderiv ℝ u'.val.toFun x v = fderiv ℝ (W f).val.toFun x v
  rw [hu']

/-- Every finite actual coordinate-word derivative commutes with the actual two-sided
inverse of the original shifted Laplacian on smooth lifts. Its actual translation and
smoothness properties are proved from the inverse identities, then the all-word theorem
applies. Source: all smooth derivatives in `lem:balanced`,
`literature/parallelizable-stable-plus-one/main.tex`. -/
theorem littlePeriodic_shiftedLaplacian_inverse_word
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (word : List (Fin a)) (g : LittlePeriodicCAlphaFunction a N 0 α)
    (hg : g.val.toFun = euclideanCoordinateWordDerivative word f.val.toFun) :
    (W g).val.toFun = euclideanCoordinateWordDerivative word (W f).val.toFun :=
  littlePeriodicCAlpha_translation_intertwiner_word hα W
    (littlePeriodic_shiftedLaplacian_inverse_translate hα W hWL hLW)
    (littlePeriodic_shiftedLaplacian_inverse_smooth hα W hWL) f hf word g hg

/-- Every genuine Finsupp multiindex derivative commutes with the actual inverse on
smooth periodic lifts. Apply the actual all-word inverse identity to the defining sorted
coordinate multiplicity word. Source: `literature/parallelizable-stable-plus-one/main.tex`,
`lem:balanced`, line385. -/
theorem littlePeriodic_shiftedLaplacian_inverse_multiindex
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (β : Fin a →₀ ℕ) (g : LittlePeriodicCAlphaFunction a N 0 α)
    (hg : g.val.toFun = euclideanCoordinateMultiindexDerivative β f.val.toFun) :
    (W g).val.toFun = euclideanCoordinateMultiindexDerivative β (W f).val.toFun :=
  littlePeriodic_shiftedLaplacian_inverse_word hα W hWL hLW f hf
    (β.toMultiset.sort (· ≤ ·)) g hg

#print axioms littlePeriodic_shiftedLaplacian_inverse_smooth
#print axioms littlePeriodic_shiftedLaplacian_inverse_directional
#print axioms littlePeriodic_shiftedLaplacian_inverse_word
#print axioms littlePeriodic_shiftedLaplacian_inverse_multiindex

end GlobalEmbedding.Paper
