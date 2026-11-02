import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateDerivativeZero
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLift

/-!
# Translation intertwining gives actual derivative intertwining

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced` proof.
DAG node: `balanced-holder-translation-intertwiner-derivative`.
-/

namespace GlobalEmbedding.Paper

/-- A bounded map intertwining actual torus translations intertwines actual derivatives
of genuine higher-order representatives. The accepted little-norm orbit derivative,
composed with the bounded map, and the genuine output orbit derivative describe the
same orbit. Frechet derivative uniqueness, evaluated at a direction, proves the result.
Source: differentiating the translation identity in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_translation_intertwiner_derivative
    {a N k l : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N l α)
    (hW : ∀ h f, W (littlePeriodicCAlphaTorusTranslate h f) =
      littlePeriodicCAlphaTorusTranslate h (W f))
    (f : LittlePeriodicCAlphaFunction a N (k + 1) α)
    (g : LittlePeriodicCAlphaFunction a N k α) (hfg : f.val.toFun = g.val.toFun)
    (u : LittlePeriodicCAlphaFunction a N (l + 1) α)
    (hug : u.val.toFun = (W g).val.toFun) (v : EuclideanSpace ℝ (Fin a)) :
    W (littlePeriodicCAlphaDirectionalDerivative v f) =
      littlePeriodicCAlphaDirectionalDerivative v u := by
  have hf := littlePeriodicCAlpha_translate_hasFDerivAt_zero f g hfg hα
  have hu := littlePeriodicCAlpha_translate_hasFDerivAt_zero u (W g) hug hα
  have hc := W.hasFDerivAt.comp 0 hf
  have hfun : (fun h : EuclideanSpace ℝ (Fin a) ↦
      W (littlePeriodicCAlphaTranslateIsometry h g)) =
      (fun h ↦ littlePeriodicCAlphaTranslateIsometry h (W g)) := by
    funext h
    simpa only [littlePeriodicCAlphaTorusTranslate_lift] using
      hW (WithLp.toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ)))) g
  change HasFDerivAt (fun h ↦ W (littlePeriodicCAlphaTranslateIsometry h g)) _ 0 at hc
  rw [hfun] at hc
  exact congrArg (fun A ↦ A v) (hc.unique hu)

#print axioms littlePeriodicCAlpha_translation_intertwiner_derivative

end GlobalEmbedding.Paper
