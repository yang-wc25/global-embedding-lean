import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLift

/-!
# Actual torus translation action laws on little Hölder space

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-torus-translation-action-laws`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Actual torus translations satisfy the zero and addition action laws.

Proof: lift torus elements to Euclidean representatives. Coordinate projection preserves
zero and addition. The every-lift formula reduces both claims to the underlying functions,
where they follow from the ordinary addition laws.
Source: actual torus shifts in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_torus_translate_laws (a N k : ℕ) (α : ℝ) :
    (∀ f : LittlePeriodicCAlphaFunction a N k α, littlePeriodicCAlphaTorusTranslate 0 f = f) ∧
    (∀ (h h' : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
      (f : LittlePeriodicCAlphaFunction a N k α),
      littlePeriodicCAlphaTorusTranslate (h + h') f =
        littlePeriodicCAlphaTorusTranslate h (littlePeriodicCAlphaTorusTranslate h' f)) := by
  constructor
  · intro f
    have hz : toLp 2 (fun i : Fin a ↦ ((0 : EuclideanSpace ℝ (Fin a)) i :
        AddCircle (1 : ℝ))) = 0 := by ext i; simp
    rw [← hz, littlePeriodicCAlphaTorusTranslate_lift]
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    change f.val.toFun (x + 0) = f.val.toFun x
    simp
  · intro h h' f
    obtain ⟨u, rfl⟩ := periodic_flat_torus_projection.surjective h
    obtain ⟨v, rfl⟩ := periodic_flat_torus_projection.surjective h'
    have hadd : toLp 2 (fun i : Fin a ↦ ((u + v) i : AddCircle (1 : ℝ))) =
        toLp 2 (fun i : Fin a ↦ (u i : AddCircle (1 : ℝ))) +
          toLp 2 (fun i : Fin a ↦ (v i : AddCircle (1 : ℝ))) := by ext i; simp
    rw [← hadd, littlePeriodicCAlphaTorusTranslate_lift, littlePeriodicCAlphaTorusTranslate_lift,
      littlePeriodicCAlphaTorusTranslate_lift]
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    change f.val.toFun (x + (u + v)) = f.val.toFun (x + u + v)
    rw [add_assoc]

#print axioms littlePeriodicCAlpha_torus_translate_laws

end GlobalEmbedding.Paper
