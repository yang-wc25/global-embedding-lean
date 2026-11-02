import GlobalEmbedding.Paper.PrincipalTorusLiftDerivatives
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSourceTranslationTransport

/-!
# Actual global source pullbacks and their induced little-space transport

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line418.
DAG node: `balanced-native-source-pullback`.
-/

open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E H EB HB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace HB B]

namespace PrincipalTorusBundle

variable {a : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ EB HB}
  {π : M → B} [IsManifold I ∞ M] [IsManifold J ∞ B]
  [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I J π)

/-- Actual inverse-chart Euclidean lifts are integer periodic because the original
period-one torus projection annihilates every integer coordinate. This needs no
regularity outside the original native chart domain. Source: torus lifts in `lem:balanced`. -/
theorem fiberEuclideanLift_integer_periodic (i : ι) (b : B)
    (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ) :
    S.fiberEuclideanLift i b (x + toLp 2 (fun j ↦ (m j : ℝ))) =
      S.fiberEuclideanLift i b x := by
  apply congrArg (S.fiberChartPoint i b)
  apply PiLp.ext
  intro j
  change ((x j + (m j : ℝ) : ℝ) : AddCircle (1 : ℝ)) = x j
  rw [AddCircle.coe_add]
  have hm : ((m j : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m j, by simp⟩
  rw [hm, add_zero]

/-- The native forward chart shift induces the negative shift of the actual Euclidean
source lift. Apply the already proved actual native overlap to quotient(x−h) and cancel
its genuine torus shift. Source: the overlap argument in `lem:balanced`, line418. -/
theorem fiberEuclideanLift_overlap_shift (i j : ι) {b : B}
    (hi : b ∈ (S.trivialization i).baseSet)
    (hj : b ∈ (S.trivialization j).baseSet)
    (h : EuclideanSpace ℝ (Fin a))
    (hh : toLp 2 (fun k ↦ (h k : AddCircle (1 : ℝ))) = S.overlapShift i j b)
    (x : EuclideanSpace ℝ (Fin a)) :
    S.fiberEuclideanLift i b (x - h) = S.fiberEuclideanLift j b x := by
  change S.fiberChartPoint i b _ = S.fiberChartPoint j b _
  rw [S.fiberChartPoint_overlap i j hi hj]
  apply congrArg (S.fiberChartPoint j b)
  rw [← hh]
  apply PiLp.ext
  intro k
  change ((x k - h k : ℝ) : AddCircle (1 : ℝ)) + h k = x k
  rw [AddCircle.coe_sub, sub_add_cancel]

/-- Genuine global pointwise sources force the actual little-data conjugacy on native
bundle overlaps; no transport equation is assumed.

Proof: choose a real lift h of the actual native overlap shift. The actual inverse-chart
overlap gives lift_j(x)=lift_i(x−h). Apply the original global source functions to that
same actual point. The existing source-translation transport theorem converts these
pointwise identities and the exact multiplier values into the actual forcing translation
and bounded operator conjugacy. Neither a compatibility hypothesis for selected solutions
nor any smoothness, inverse, range, or value-at-zero restriction is needed here.
Source: uniqueness and chart translation in `lem:balanced`, line418. -/
theorem source_little_data_overlap {R N k : ℕ} {α : ℝ}
    (i j : ι) {b : B}
    (hi : b ∈ (S.trivialization i).baseSet)
    (hj : b ∈ (S.trivialization j).baseSet)
    (sourceA : M → EuclideanSpace ℝ (Fin R) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : M → EuclideanSpace ℝ (Fin N))
    (forcing₁ forcing₂ : LittlePeriodicCAlphaFunction a N k α)
    (ops₁ ops₂ : LittlePeriodicCAlphaFunction a R k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α)
    (hf₁ : ∀ x, forcing₁.val.toFun x = sourcef (S.fiberEuclideanLift i b x))
    (hf₂ : ∀ x, forcing₂.val.toFun x = sourcef (S.fiberEuclideanLift j b x))
    (hA₁ : ∀ (u : LittlePeriodicCAlphaFunction a R k α) x,
      (ops₁ u).val.toFun x = sourceA (S.fiberEuclideanLift i b x) (u.val.toFun x))
    (hA₂ : ∀ (u : LittlePeriodicCAlphaFunction a R k α) x,
      (ops₂ u).val.toFun x = sourceA (S.fiberEuclideanLift j b x) (u.val.toFun x)) :
    forcing₂ = littlePeriodicCAlphaTorusTranslate (-S.overlapShift i j b) forcing₁ ∧
      ops₂ = (littlePeriodicCAlphaTorusTranslate (N := N) (k := k) (α := α)
        (-S.overlapShift i j b)).toContinuousLinearMap.comp
          (ops₁.comp (littlePeriodicCAlphaTorusTranslate (N := R) (k := k) (α := α)
            (S.overlapShift i j b)).toContinuousLinearMap) := by
  obtain ⟨h, hh⟩ := periodic_flat_torus_projection.surjective (S.overlapShift i j b)
  have hpoint (x : EuclideanSpace ℝ (Fin a)) :=
    S.fiberEuclideanLift_overlap_shift i j hi hj h hh x
  have ht := littlePeriodicCAlpha_source_translation_transport h
    (fun x ↦ sourceA (S.fiberEuclideanLift i b x))
    (fun x ↦ sourceA (S.fiberEuclideanLift j b x))
    forcing₁ forcing₂ ops₁ ops₂ hA₁ hA₂
    (fun x ↦ (hf₂ x).trans ((congrArg sourcef (hpoint x)).symm.trans (hf₁ (x - h)).symm))
    (fun x ↦ (congrArg sourceA (hpoint x)).symm)
  simpa only [hh] using ht

#print axioms fiberEuclideanLift_integer_periodic
#print axioms fiberEuclideanLift_overlap_shift
#print axioms source_little_data_overlap

end PrincipalTorusBundle
end GlobalEmbedding.Paper
