import GlobalEmbedding.Paper.BalancedHolderSmoothTranslatedFamily
import GlobalEmbedding.Paper.BalancedHolderMultiplicationBounded
import GlobalEmbedding.Paper.LittlePeriodicCAlphaMultiplierTranslate

/-!
# Actual smooth translated forcing and conjugated coefficient operators

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-fixed-translated-data`.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Smooth source forcing and actual operator-valued coefficients on an open local parameter
domain give actual little C^{2,α} data with genuinely joint norm-smooth translations and
conjugated multiplier operators.

Use the proved faithful Hilbert–Schmidt inverse to turn each ACTUAL value operator into its
Euclidean coefficient vector. This is a finite-dimensional continuous linear operation, so
source smoothness and periodicity persist. The full open-domain smooth-family theorem
constructs both actual forcing and coefficient slices and proves their joint shift smoothness.
Compose translated coefficients with the actual bounded multiplier CLM. Actual translation
conjugacy identifies this smooth operator-valued map with τ_h A_p τ_{−h}. No source slice
membership, coefficient representation or operator-valued smoothness is assumed.
Source: translated vertical difference quotients in the proof of `lem:balanced`. -/
theorem balanced_fixed_translated_data {q a M N : ℕ} {α : ℝ}
    (U : Set (EuclideanSpace ℝ (Fin q))) (hU : IsOpen U)
    (A : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin a) →
      (EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    (f : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A)
      (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f)
      (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))))
    (hAperiodic : ∀ p ∈ U, ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
      A p (x + toLp 2 (fun i ↦ (m i : ℝ))) = A p x)
    (hfperiodic : ∀ p ∈ U, ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
      f p (x + toLp 2 (fun i ↦ (m i : ℝ))) = f p x)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ forcing : EuclideanSpace ℝ (Fin q) → LittlePeriodicCAlphaFunction a N 2 α,
      ∃ ops : EuclideanSpace ℝ (Fin q) →
          (LittlePeriodicCAlphaFunction a M 2 α →L[ℝ] LittlePeriodicCAlphaFunction a N 2 α),
        (∀ p ∈ U, ∀ x, (forcing p).val.toFun x = f p x) ∧
        (∀ p ∈ U, ∀ (u : LittlePeriodicCAlphaFunction a M 2 α) x,
          (ops p u).val.toFun x = A p x (u.val.toFun x)) ∧
        ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin a) ↦
          littlePeriodicCAlphaTranslateIsometry z.2 (forcing z.1))
          (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))) ∧
        ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin a) ↦
          (littlePeriodicCAlphaTranslateIsometry
            (N := N) (k := 2) (α := α) z.2).toContinuousLinearMap.comp
            ((ops z.1).comp (littlePeriodicCAlphaTranslateIsometry
              (N := M) (k := 2) (α := α) (-z.2)).toContinuousLinearMap))
          (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))) := by
  let e := hilbertSchmidtCoordinateEquiv M N
  let inv : (EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ]
      EuclideanSpace ℝ (Fin (N * M)) := e.symm.toLinearMap.toContinuousLinearMap
  let C (p : EuclideanSpace ℝ (Fin q)) (x : EuclideanSpace ℝ (Fin a)) := inv (A p x)
  have hC : ContDiffOn ℝ ∞ (Function.uncurry C)
      (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin a)))) :=
    inv.contDiff.comp_contDiffOn hA
  have hCperiodic : ∀ p ∈ U, ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
      C p (x + toLp 2 (fun i ↦ (m i : ℝ))) = C p x := by
    intro p hp x m
    change inv (A p (x + toLp 2 (fun i ↦ (m i : ℝ)))) = inv (A p x)
    rw [hAperiodic p hp x m]
  obtain ⟨g, hgvalue, hgsmooth, hgjoint⟩ :=
    balanced_holder_smooth_translated_family (k := 2) U hU f hf hfperiodic hα0 hα1
  obtain ⟨c, hcvalue, hcsmooth, hcjoint⟩ :=
    balanced_holder_smooth_translated_family (k := 2) U hU C hC hCperiodic hα0 hα1
  obtain ⟨hfaithful, hnorm, mult, hmult, hbound⟩ :=
    balanced_holder_multiplication_bounded (a := a) (M := M) (N := N) (k := 2) hα0 hα1
  let ops (p : EuclideanSpace ℝ (Fin q)) := mult (c p)
  refine ⟨g, ops, fun p hp x ↦ congrFun (hgvalue p hp) x, ?_, hgjoint, ?_⟩
  · intro p hp u x
    change (mult (c p) u).val.toFun x = A p x (u.val.toFun x)
    rw [hmult, hcvalue p hp]
    change e (e.symm (A p x)) (u.val.toFun x) = A p x (u.val.toFun x)
    rw [e.apply_symm_apply]
  · have hmultSmooth : ContDiff ℝ ∞ mult :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := LittlePeriodicCAlphaFunction a (N * M) 2 α)
        (F := LittlePeriodicCAlphaFunction a M 2 α →L[ℝ] LittlePeriodicCAlphaFunction a N 2 α) mult
    have hs := hmultSmooth.comp_contDiffOn hcjoint
    apply hs.congr
    intro z hz
    exact littlePeriodicCAlpha_multiplier_translate mult hmult (c z.1) z.2

#print axioms balanced_fixed_translated_data

end GlobalEmbedding.Paper
