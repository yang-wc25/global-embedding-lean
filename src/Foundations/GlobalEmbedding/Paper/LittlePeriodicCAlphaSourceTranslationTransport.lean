import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLift

/-!
# Actual Banach data transport from the original pointwise source chart relations

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–425.
DAG node: `balanced-holder-source-translation-transport`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Original pointwise source chart relations imply the actual inverse-shifted Banach data.

The projection of minus h is the negative actual torus shift. The genuine every-lift action
formula identifies both actual torus operators with actual Euclidean translations. Actual
lift injectivity proves the forcing equality. At an arbitrary input and point x, conjugating
the first actual multiplier gives A1(x−h)u(x−h+h)=A2(x)u(x); operator extensionality proves
the actual conjugacy. No operator conjugacy or coefficient representation is assumed.
Source: inverse transport of local data across forward principal-torus chart translations
at the end of the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_source_translation_transport {a R N k : ℕ} {α : ℝ}
    (h : EuclideanSpace ℝ (Fin a))
    (A₁ A₂ : EuclideanSpace ℝ (Fin a) →
      (EuclideanSpace ℝ (Fin R) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    (forcing₁ forcing₂ : LittlePeriodicCAlphaFunction a N k α)
    (ops₁ ops₂ : LittlePeriodicCAlphaFunction a R k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α)
    (hops₁ : ∀ (u : LittlePeriodicCAlphaFunction a R k α) x,
      (ops₁ u).val.toFun x = A₁ x (u.val.toFun x))
    (hops₂ : ∀ (u : LittlePeriodicCAlphaFunction a R k α) x,
      (ops₂ u).val.toFun x = A₂ x (u.val.toFun x))
    (hforcing : ∀ x, forcing₂.val.toFun x = forcing₁.val.toFun (x - h))
    (hcoeff : ∀ x, A₂ x = A₁ (x - h)) :
    let delta := toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ)));
    forcing₂ = littlePeriodicCAlphaTorusTranslate (-delta) forcing₁ ∧
      ops₂ = (littlePeriodicCAlphaTorusTranslate (N := N) (k := k) (α := α)
        (-delta)).toContinuousLinearMap.comp
          (ops₁.comp (littlePeriodicCAlphaTorusTranslate (N := R) (k := k) (α := α)
            delta).toContinuousLinearMap) := by
  dsimp only
  have hneg : toLp 2 (fun i : Fin a ↦ ((-h) i : AddCircle (1 : ℝ))) =
      -toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ))) := by
    ext i
    simp
  simp only [← hneg, littlePeriodicCAlphaTorusTranslate_lift]
  constructor
  · apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    change forcing₂.val.toFun x = forcing₁.val.toFun (x + -h)
    simpa only [sub_eq_add_neg] using hforcing x
  · apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    change (ops₂ u).val.toFun x =
      (ops₁ (littlePeriodicCAlphaTranslateIsometry h u)).val.toFun (x + -h)
    rw [hops₂, hops₁]
    change A₂ x (u.val.toFun x) = A₁ (x + -h) (u.val.toFun (x + -h + h))
    rw [hcoeff]
    simp only [sub_eq_add_neg, neg_add_cancel_right]

#print axioms littlePeriodicCAlpha_source_translation_transport

end GlobalEmbedding.Paper
