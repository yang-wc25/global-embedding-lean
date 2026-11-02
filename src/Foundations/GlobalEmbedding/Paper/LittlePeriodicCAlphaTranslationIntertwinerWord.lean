import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslationIntertwinerDerivative
import GlobalEmbedding.Paper.EuclideanCoordinateWordSmoothPeriodic
import GlobalEmbedding.Paper.EuclideanCoordinateMultiindexDerivative
import GlobalEmbedding.Paper.PeriodicCAlphaSmoothUpgrade
import GlobalEmbedding.Paper.SmoothPeriodicLittleMembership

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A bounded translation intertwiner preserving genuine smooth lifts commutes with
all actual coordinate-word derivatives on smooth lifts. Induct on the word. Genuine
smooth membership gives an original little representative of the tail derivative;
smooth upgrade gives actual higher-order representatives of it and its W image.
The actual directional intertwining theorem and original lift formulas perform the
next coordinate differentiation. Source: all derivatives in the proof of `lem:balanced`,
`literature/parallelizable-stable-plus-one/main.tex`. -/
theorem littlePeriodicCAlpha_translation_intertwiner_word
    {a N k l : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N l α)
    (hW : ∀ h f, W (littlePeriodicCAlphaTorusTranslate h f) =
      littlePeriodicCAlphaTorusTranslate h (W f))
    (hWs : ∀ f, ContDiff ℝ ∞ f.val.toFun → ContDiff ℝ ∞ (W f).val.toFun)
    (f : LittlePeriodicCAlphaFunction a N k α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (word : List (Fin a)) (g : LittlePeriodicCAlphaFunction a N k α)
    (hg : g.val.toFun = euclideanCoordinateWordDerivative word f.val.toFun) :
    (W g).val.toFun = euclideanCoordinateWordDerivative word (W f).val.toFun := by
  induction word generalizing g with
  | nil =>
      have hgf : g = f := by
        apply Subtype.ext
        apply periodicCAlpha_toFun_injective
        exact hg
      rw [hgf]
      rfl
  | cons i word ih =>
      obtain ⟨hs, hp⟩ := euclideanCoordinateWordDerivative_smooth_periodic
        word f.val.toFun hf f.val.periodic
      obtain ⟨t, ht⟩ := smooth_periodic_little_membership
        (euclideanCoordinateWordDerivative word f.val.toFun) hs hp hα k
      have hts : ContDiff ℝ ∞ t.val.toFun := by rw [ht]; exact hs
      have hWt := ih t ht
      obtain ⟨t', ht'⟩ := periodicCAlpha_smooth_upgrade t.val hts hα (k + 1)
      obtain ⟨u', hu'⟩ := periodicCAlpha_smooth_upgrade (W t).val (hWs t hts) hα (l + 1)
      have hD := littlePeriodicCAlpha_translation_intertwiner_derivative
        hα W hW t' t ht' u' hu' (EuclideanSpace.single i 1)
      have htg : littlePeriodicCAlphaDirectionalDerivative (EuclideanSpace.single i 1) t' =
          g := by
        apply Subtype.ext
        apply periodicCAlpha_toFun_injective
        funext x
        change fderiv ℝ t'.val.toFun x (EuclideanSpace.single i 1) = g.val.toFun x
        rw [ht', ht, hg]
        rfl
      funext x
      rw [← htg, hD]
      change fderiv ℝ u'.val.toFun x (EuclideanSpace.single i 1) =
        fderiv ℝ (euclideanCoordinateWordDerivative word (W f).val.toFun) x
          (EuclideanSpace.single i 1)
      rw [hu', hWt]

/-- The actual Finsupp multiindex derivative also commutes with a smoothness-preserving
bounded translation intertwiner. Apply the all-word result to the actual sorted coordinate
multiplicity word defining that derivative. Source: smooth derivative commutation in the
proof of `lem:balanced`, `literature/parallelizable-stable-plus-one/main.tex`. -/
theorem littlePeriodicCAlpha_translation_intertwiner_multiindex
    {a N k l : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N l α)
    (hW : ∀ h f, W (littlePeriodicCAlphaTorusTranslate h f) =
      littlePeriodicCAlphaTorusTranslate h (W f))
    (hWs : ∀ f, ContDiff ℝ ∞ f.val.toFun → ContDiff ℝ ∞ (W f).val.toFun)
    (f : LittlePeriodicCAlphaFunction a N k α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (β : Fin a →₀ ℕ) (g : LittlePeriodicCAlphaFunction a N k α)
    (hg : g.val.toFun = euclideanCoordinateMultiindexDerivative β f.val.toFun) :
    (W g).val.toFun = euclideanCoordinateMultiindexDerivative β (W f).val.toFun :=
  littlePeriodicCAlpha_translation_intertwiner_word hα W hW hWs f hf
    (β.toMultiset.sort (· ≤ ·)) g hg

#print axioms littlePeriodicCAlpha_translation_intertwiner_word
#print axioms littlePeriodicCAlpha_translation_intertwiner_multiindex

end GlobalEmbedding.Paper
