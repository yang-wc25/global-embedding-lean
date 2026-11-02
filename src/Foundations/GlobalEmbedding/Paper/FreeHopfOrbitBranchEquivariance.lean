import GlobalEmbedding.Paper.FreeHopfProductAction
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSourceTranslationTransport
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateFixedUnique

/-!
# Genuine orbit-source translation and strict-small branch covariance

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines417–418 and477–495.
DAG node: `free-hopf-orbit-branch-equivariance`.
-/

noncomputable section

open WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual composition of the same multi-action gives exactly the translated orbit. -/
theorem freeHopfRealAction_orbit_shift {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) (s y : EuclideanSpace ℝ (Fin a)) :
    freeHopfRealAction C (fun i ↦ y i) (freeHopfRealAction C (fun i ↦ s i) x) =
      freeHopfRealAction C (fun i ↦ (y - -s) i) x := by
  rw [← freeHopfRealAction_add]
  congr 1
  funext i
  simp only [sub_neg_eq_add, PiLp.add_apply, Pi.add_apply]

/-- The same actual global orbit sources force exact little-data transport.

Proof: actual action addition identifies the shifted-point orbit with the original orbit
translated in its real parameter. Apply the already accepted point-source translation
transport theorem, and identify the actual quotient torus shifts with their real lifts.
No multiplier conjugacy or compatibility is an input.
Source: the uniqueness/descent step of lem:balanced, lines417–418. -/
theorem freeHopf_orbit_little_data_translate {a d N k : ℕ} {α : ℝ}
    (C : Fin a → ℕ) (x : FreeHopfProduct C) (s : EuclideanSpace ℝ (Fin a))
    (sourceA : FreeHopfProduct C → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (sourcef : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (f₁ f₂ : LittlePeriodicCAlphaFunction a N k α)
    (A₁ A₂ : LittlePeriodicCAlphaFunction a d k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α)
    (hf₁ : ∀ y, f₁.val.toFun y = sourcef (freeHopfRealAction C (fun i ↦ y i) x))
    (hf₂ : ∀ y, f₂.val.toFun y = sourcef (freeHopfRealAction C (fun i ↦ y i)
      (freeHopfRealAction C (fun i ↦ s i) x)))
    (hA₁ : ∀ u y, (A₁ u).val.toFun y =
      sourceA (freeHopfRealAction C (fun i ↦ y i) x) (u.val.toFun y))
    (hA₂ : ∀ u y, (A₂ u).val.toFun y = sourceA (freeHopfRealAction C (fun i ↦ y i)
      (freeHopfRealAction C (fun i ↦ s i) x)) (u.val.toFun y)) :
    f₂ = littlePeriodicCAlphaTranslateIsometry s f₁ ∧
      A₂ = (littlePeriodicCAlphaTranslateIsometry (N := N) (k := k) (α := α)
        s).toContinuousLinearMap.comp
          (A₁.comp (littlePeriodicCAlphaTranslateIsometry (N := d) (k := k) (α := α)
            (-s)).toContinuousLinearMap) := by
  have ht := littlePeriodicCAlpha_source_translation_transport (-s)
    (fun y ↦ sourceA (freeHopfRealAction C (fun i ↦ y i) x))
    (fun y ↦ sourceA (freeHopfRealAction C (fun i ↦ y i)
      (freeHopfRealAction C (fun i ↦ s i) x))) f₁ f₂ A₁ A₂ hA₁ hA₂
    (fun y ↦ (hf₂ y).trans ((congrArg sourcef (freeHopfRealAction_orbit_shift C x s y))
      |>.trans (hf₁ (y - -s)).symm))
    (fun y ↦ congrArg sourceA (freeHopfRealAction_orbit_shift C x s y))
  have hneg : -(toLp 2 (fun i : Fin a ↦ ((-s) i : AddCircle (1 : ℝ)))) =
      toLp 2 (fun i : Fin a ↦ (s i : AddCircle (1 : ℝ))) := by
    apply PiLp.ext
    intro i
    change -((-s i : ℝ) : AddCircle (1 : ℝ)) = (s i : AddCircle (1 : ℝ))
    rw [AddCircle.coe_neg, neg_neg]
  dsimp only at ht
  rw [hneg] at ht
  simpa only [littlePeriodicCAlphaTorusTranslate_lift] using ht

/-- Actual strict-small solutions over orbit-related points necessarily translate.

Proof: the original source values force genuine forcing/multiplier translation by the
preceding theorem. Rewrite the second actual fixed equation and strict bound with those
identities. Apply the accepted actual translated strict-small uniqueness theorem. Neither
branch compatibility nor equivariance of a desired correction is assumed.
Source: the uniqueness mechanism in lem:balanced, lines417–418. -/
theorem freeHopf_orbit_fixed_branch_translate {a d N k : ℕ} {α : ℝ}
    (C : Fin a → ℕ) (x : FreeHopfProduct C) (s : EuclideanSpace ℝ (Fin a))
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a d k α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (sourceA : FreeHopfProduct C → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (sourcef : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (f₁ f₂ v₁ v₂ : LittlePeriodicCAlphaFunction a N k α)
    (A₁ A₂ : LittlePeriodicCAlphaFunction a d k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α)
    (hf₁ : ∀ y, f₁.val.toFun y = sourcef (freeHopfRealAction C (fun i ↦ y i) x))
    (hf₂ : ∀ y, f₂.val.toFun y = sourcef (freeHopfRealAction C (fun i ↦ y i)
      (freeHopfRealAction C (fun i ↦ s i) x)))
    (hA₁ : ∀ u y, (A₁ u).val.toFun y =
      sourceA (freeHopfRealAction C (fun i ↦ y i) x) (u.val.toFun y))
    (hA₂ : ∀ u y, (A₂ u).val.toFun y = sourceA (freeHopfRealAction C (fun i ↦ y i)
      (freeHopfRealAction C (fun i ↦ s i) x)) (u.val.toFun y))
    (hv₁ : v₁ = f₁ + A₁ (Q v₁ v₁)) (hv₂ : v₂ = f₂ + A₂ (Q v₂ v₂))
    (hs₁ : ‖(2 : ℝ) • A₁.comp (Q v₁)‖ < 1)
    (hs₂ : ‖(2 : ℝ) • A₂.comp (Q v₂)‖ < 1) :
    v₂ = littlePeriodicCAlphaTranslateIsometry s v₁ := by
  obtain ⟨hf, hA⟩ := freeHopf_orbit_little_data_translate C x s
    sourceA sourcef f₁ f₂ A₁ A₂ hf₁ hf₂ hA₁ hA₂
  apply littlePeriodicCAlpha_translate_fixed_unique Q hQsym hQτ A₁ f₁ v₁ v₂ s hv₁ hs₁
  · rw [← hf, ← hA]
    exact hv₂
  · rw [← hA]
    exact hs₂

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopf_orbit_little_data_translate
#print axioms GlobalEmbedding.Paper.freeHopf_orbit_fixed_branch_translate
