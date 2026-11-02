import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaSupremumBounds
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Bounded target maps on the actual periodic Hölder spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Constant real target maps provide the realification operations needed
for complex Hölder scalars and real/imaginary projections. This is distinct from translation
in the spatial variable and from multiplication by a nonconstant coefficient.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A bounded real linear target map acts by actual pointwise postcomposition on the ambient
periodic Hölder space and on its actual little closure, with operator norm at most ‖A‖.

Source: Proposition `prop:collar`, proof lines 530–534, realification of complex coefficients.
Every iterated derivative of A∘f is A postcomposed with that of f, and the same holds for the
jet difference in the top Hölder quotient. Operator norm bounds therefore construct the raw
carrier element and bound each actual supremum by ‖A‖ times the old supremum. Nonnegative
upper bounds handle the empty quotient set. Summing gives the full original norm estimate.
Pointwise operation laws and carrier extensionality make this a linear map, and the norm
estimate makes it continuous. It preserves smooth lifts, so continuity maps the closure of
the smooth submodule into the corresponding little closure. Restriction gives the claimed
actual little-space map and the same norm estimate. No completeness is required.
-/
theorem collar_holder_target_map {a N M k : ℕ} {α : ℝ}
    (A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin M)) :
    ∃ (T : PeriodicCAlphaFunction a N k α →L[ℝ] PeriodicCAlphaFunction a M k α)
      (L : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
        LittlePeriodicCAlphaFunction a M k α),
      (∀ f, (T f).toFun = A ∘ f.toFun) ∧ ‖T‖ ≤ ‖A‖ ∧
      (∀ f, (L f : PeriodicCAlphaFunction a M k α).toFun =
        A ∘ (f : PeriodicCAlphaFunction a N k α).toFun) ∧ ‖L‖ ≤ ‖A‖ := by
  have hjet (f : PeriodicCAlphaFunction a N k α) (j : ℕ) (hj : j ≤ k)
      (x : EuclideanSpace ℝ (Fin a)) :
      iteratedFDeriv ℝ j (A ∘ f.toFun) x =
        A.compContinuousMultilinearMap (iteratedFDeriv ℝ j f.toFun x) :=
    A.iteratedFDeriv_comp_left f.contDiff.contDiffAt (by exact_mod_cast hj)
  have hjetnorm (f : PeriodicCAlphaFunction a N k α) (j : ℕ) (hj : j ≤ k)
      (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ j (A ∘ f.toFun) x‖ ≤ ‖A‖ * ‖iteratedFDeriv ℝ j f.toFun x‖ := by
    rw [hjet f j hj x]
    exact A.norm_compContinuousMultilinearMap_le _
  have hdiffnorm (f : PeriodicCAlphaFunction a N k α)
      (x y : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ k (A ∘ f.toFun) x - iteratedFDeriv ℝ k (A ∘ f.toFun) y‖ ≤
        ‖A‖ * ‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ := by
    rw [hjet f k le_rfl x, hjet f k le_rfl y]
    have heq : A.compContinuousMultilinearMap (iteratedFDeriv ℝ k f.toFun x) -
        A.compContinuousMultilinearMap (iteratedFDeriv ℝ k f.toFun y) =
        A.compContinuousMultilinearMap
          (iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y) := by
      ext m
      simp
    rw [heq]
    exact A.norm_compContinuousMultilinearMap_le _
  let t : PeriodicCAlphaFunction a N k α → PeriodicCAlphaFunction a M k α := fun f ↦
    { toFun := A ∘ f.toFun
      periodic := by intro x n; simp only [Function.comp_apply, f.periodic]
      contDiff := A.contDiff.comp f.contDiff
      derivative_bounded := by
        intro j hj
        obtain ⟨C, hC⟩ := f.derivative_bounded j hj
        exact ⟨‖A‖ * C, fun x hx ↦ (hjetnorm f j hj x).trans
          (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg A))⟩
      holder_bounded := by
        obtain ⟨C, hC⟩ := f.holder_bounded
        refine ⟨‖A‖ * C, fun x y hd ↦ ?_⟩
        calc
          _ ≤ (‖A‖ * ‖iteratedFDeriv ℝ k f.toFun x -
              iteratedFDeriv ℝ k f.toFun y‖) / _ :=
            div_le_div_of_nonneg_right (hdiffnorm f x y) (Real.rpow_nonneg hd.le _)
          _ = ‖A‖ * (_ / _) := mul_div_assoc _ _ _
          _ ≤ ‖A‖ * C := mul_le_mul_of_nonneg_left (hC x y hd) (norm_nonneg A) }
  have hnorm (f : PeriodicCAlphaFunction a N k α) : ‖t f‖ ≤ ‖A‖ * ‖f‖ := by
    change periodicCAlphaNorm (t f) ≤ ‖A‖ * periodicCAlphaNorm f
    unfold periodicCAlphaNorm
    rw [mul_add, Finset.mul_sum]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      apply Real.sSup_le _
      · apply mul_nonneg (norm_nonneg A)
        apply Real.sSup_nonneg
        rintro r ⟨x, hx, rfl⟩
        exact norm_nonneg _
      · rintro r ⟨x, hx, rfl⟩
        exact (hjetnorm f j hjk x).trans (mul_le_mul_of_nonneg_left
          (le_csSup ((periodicCAlpha_supremum_bounds f).1 j hjk) ⟨x, hx, rfl⟩)
          (norm_nonneg A))
    · apply Real.sSup_le _
      · apply mul_nonneg (norm_nonneg A)
        apply Real.sSup_nonneg
        rintro r ⟨x, y, hd, rfl⟩
        exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hd.le _)
      · rintro r ⟨x, y, hd, rfl⟩
        calc
          _ ≤ (‖A‖ * ‖iteratedFDeriv ℝ k f.toFun x -
              iteratedFDeriv ℝ k f.toFun y‖) / _ :=
            div_le_div_of_nonneg_right (hdiffnorm f x y) (Real.rpow_nonneg hd.le _)
          _ = ‖A‖ * (_ / _) := mul_div_assoc _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (le_csSup (periodicCAlpha_supremum_bounds f).2 ⟨x, y, hd, rfl⟩)
            (norm_nonneg A)
  let T₀ : PeriodicCAlphaFunction a N k α →ₗ[ℝ] PeriodicCAlphaFunction a M k α :=
    { toFun := t
      map_add' := by
        intro f g
        apply periodicCAlpha_toFun_injective
        funext x
        change A ((f + g).toFun x) = (t f + t g).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.1,
          (periodicCAlpha_pointwise_operations a M k α).2.1]
        exact A.map_add _ _
      map_smul' := by
        intro c f
        apply periodicCAlpha_toFun_injective
        funext x
        change A ((c • f).toFun x) = (c • t f).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.2,
          (periodicCAlpha_pointwise_operations a M k α).2.2]
        exact A.map_smul c _ }
  let T := T₀.mkContinuous ‖A‖ hnorm
  have hmaps : MapsTo T (smoothPeriodicCAlphaSubmodule a N k α)
      (smoothPeriodicCAlphaSubmodule a M k α) := by
    intro f hf
    exact A.contDiff.comp (show ContDiff ℝ ∞ f.toFun from hf)
  have hclosure := hmaps.closure T.continuous
  let L₀ : LittlePeriodicCAlphaFunction a N k α →ₗ[ℝ]
      LittlePeriodicCAlphaFunction a M k α :=
    { toFun := fun f ↦ ⟨T f.val, hclosure f.property⟩
      map_add' := by intro f g; apply Subtype.ext; exact T.map_add f.val g.val
      map_smul' := by intro c f; apply Subtype.ext; exact T.map_smul c f.val }
  have hL (f : LittlePeriodicCAlphaFunction a N k α) : ‖L₀ f‖ ≤ ‖A‖ * ‖f‖ :=
    hnorm f.val
  exact ⟨T, L₀.mkContinuous ‖A‖ hL, fun _ ↦ rfl,
    T₀.mkContinuous_norm_le (norm_nonneg A) hnorm, fun _ ↦ rfl,
    L₀.mkContinuous_norm_le (norm_nonneg A) hL⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_holder_target_map
