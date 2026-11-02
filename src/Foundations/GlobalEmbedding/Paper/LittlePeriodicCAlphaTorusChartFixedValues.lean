import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateFixedUnique
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusValue
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLaws

/-!
# Actual strictly small quadratic fixed points give matching torus chart values

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-torus-chart-fixed-values`.
-/

namespace GlobalEmbedding.Paper

/-- A strictly small solution of the inverse-translated actual equation has the same actual
values in the forward-translated torus chart.

Choose an actual Euclidean lift of the chart shift. The accepted strict-fixed uniqueness
identifies w with the inverse translate of v, using the actual translated forcing and
conjugated coefficient. Actual torus action addition then cancels the two shifts in value
evaluation. The negative sign is essential: chart q↦q+delta corresponds to function
translation by minus delta. Source: overlap uniqueness in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_torus_chart_fixed_values {a M N k : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a M k α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (A : LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α)
    (f v w : LittlePeriodicCAlphaFunction a N k α)
    (delta : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (hv : v = f + A (Q v v)) (hsv : ‖(2 : ℝ) • A.comp (Q v)‖ < 1) :
    let TX := littlePeriodicCAlphaTorusTranslate (N := N) (k := k) (α := α) (-delta)
    let SY := littlePeriodicCAlphaTorusTranslate (N := M) (k := k) (α := α) delta
    let Ah := TX.toContinuousLinearMap.comp (A.comp SY.toContinuousLinearMap)
    w = TX f + Ah (Q w w) → ‖(2 : ℝ) • Ah.comp (Q w)‖ < 1 →
      ∀ q : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)),
        littlePeriodicCAlphaTorusValue w (q + delta) = littlePeriodicCAlphaTorusValue v q := by
  dsimp only
  intro hw hsw q
  have hwv : w = littlePeriodicCAlphaTorusTranslate (-delta) v := by
    obtain ⟨h, rfl⟩ := periodic_flat_torus_projection.surjective delta
    have hneg : WithLp.toLp 2 (fun i : Fin a ↦ ((-h) i : AddCircle (1 : ℝ))) =
        -WithLp.toLp 2 (fun i : Fin a ↦ (h i : AddCircle (1 : ℝ))) := by
      ext i
      simp
    simp only [← hneg, littlePeriodicCAlphaTorusTranslate_lift] at hw hsw ⊢
    apply littlePeriodicCAlpha_translate_fixed_unique Q hQsym hQτ A f v w (-h) hv hsv
    · simpa only [neg_neg] using hw
    · simpa only [neg_neg] using hsw
  rw [hwv]
  unfold littlePeriodicCAlphaTorusValue
  rw [← (littlePeriodicCAlpha_torus_translate_laws a N k α).2 (q + delta) (-delta) v]
  rw [add_neg_cancel_right]

#print axioms littlePeriodicCAlpha_torus_chart_fixed_values

end GlobalEmbedding.Paper
