import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Actual Fréchet Taylor polynomials along a line

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
and the low-order part of `repair-local-convolution-estimates`.

The one-variable Taylor theorem is applied to `t ↦ u (x + t • v)`.
Its iterated derivatives are identified with the actual Fréchet
derivatives of `u` evaluated repeatedly on `v`. This gives a vector-valued
remainder bound from a derivative bound only on the indicated segment.
-/

open scoped BigOperators ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual restriction of a map to an affine line. -/
def lineProfile (u : E → F) (x v : E) (t : ℝ) : F := u (x + t • v)

/-- The actual Taylor polynomial, evaluated at an increment `v`, expressed
using the native iterated Fréchet derivatives and their factorials. -/
def frechetTaylor (u : E → F) (n : ℕ) (x v : E) : F :=
  ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ k u x (fun _ => v)

/-- Restriction of a `C^n` map to a line is `C^n`. -/
theorem lineProfile_contDiff {u : E → F} {n : ℕ∞ω}
    (hu : ContDiff ℝ n u) (x v : E) : ContDiff ℝ n (lineProfile u x v) :=
  hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- The `k`th derivative along a line is the true `k`th Fréchet derivative
evaluated in `k` copies of the direction. -/
theorem lineProfile_iteratedDeriv {u : E → F} {n : ℕ∞ω}
    (hu : ContDiff ℝ n u) (x v : E) (k : ℕ) (hk : k ≤ n) (t : ℝ) :
    iteratedDeriv k (lineProfile u x v) t =
      iteratedFDeriv ℝ k u (x + t • v) (fun _ => v) := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ v
  have hshift : ContDiff ℝ n (fun z : E => u (x + z)) :=
    hu.comp (contDiff_const.add contDiff_id)
  have hcomp := L.iteratedFDeriv_comp_right
    hshift t hk
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ k ((fun z => u (x + z)) ∘ L) t) (fun _ => 1) = _
  rw [hcomp, iteratedFDeriv_comp_add_left]
  simp [L, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- On the unit segment, the native one-variable Taylor polynomial equals
the explicit Fréchet Taylor polynomial at the actual increment. -/
theorem taylorWithinEval_lineProfile {u : E → F} {n : ℕ}
    (hu : ContDiff ℝ n u) (x v : E) :
    taylorWithinEval (lineProfile u x v) n (Set.Icc (0 : ℝ) 1) 0 1 =
      frechetTaylor u n x v := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkn' : (k : ℕ∞ω) ≤ n := by exact_mod_cast hkn
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    (((lineProfile_contDiff hu x v).of_le hkn').contDiffAt) (by simp)]
  rw [lineProfile_iteratedDeriv hu x v k hkn' 0]
  simp

/-- A derivative bound on the actual segment gives a quantitative Fréchet
Taylor remainder. The denominator `n!` is the (nonsharp) constant supplied
by Mathlib's vector-valued Taylor estimate. -/
theorem norm_sub_frechetTaylor_le {u : E → F} {n : ℕ}
    (hu : ContDiff ℝ (n + 1) u) (x v : E) (B : ℝ)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) u (x + t • v)‖ ≤ B) :
    ‖u (x + v) - frechetTaylor u n x v‖ ≤
      B * ‖v‖ ^ (n + 1) / (n.factorial : ℝ) := by
  have hprof := lineProfile_contDiff hu x v
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) (lineProfile u x v) (Set.Icc (0 : ℝ) 1) t‖ ≤
        B * ‖v‖ ^ (n + 1) := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      hprof.contDiffAt ht]
    rw [lineProfile_iteratedDeriv hu x v (n + 1) le_rfl t]
    have hop := (iteratedFDeriv ℝ (n + 1) u (x + t • v)).le_opNorm (fun _ => v)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hop
    exact hop.trans (mul_le_mul_of_nonneg_right (hB t ht) (pow_nonneg (norm_nonneg v) _))
  have ht := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := 1) (x := 1)
    zero_le_one hprof.contDiffOn (by simp) hderiv
  have hle : (n : ℕ∞ω) ≤ n + 1 := by exact_mod_cast Nat.le_succ n
  rw [taylorWithinEval_lineProfile (hu.of_le hle) x v] at ht
  simpa only [lineProfile, one_smul, sub_zero, one_pow, mul_one] using ht

/-- A genuinely local Taylor estimate: regularity is required only at
points on the actual segment. The proof uses Mathlib's multivariate
integral remainder and bounds its native multilinear integrand. -/
theorem norm_sub_frechetTaylor_le_of_contDiffAt [CompleteSpace F]
    {u : E → F} {n : ℕ} (x v : E) (B : ℝ)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) u (x + t • v))
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) u (x + t • v)‖ ≤ B) :
    ‖u (x + v) - frechetTaylor u n x v‖ ≤
      B * ‖v‖ ^ (n + 1) / (n.factorial : ℝ) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv hu
  change u (x + v) = frechetTaylor u n x v + _ at hTaylor
  rw [hTaylor, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1 - t)^n • iteratedFDeriv ℝ (n + 1) u (x + t • v) (fun _ => v)‖ ≤
        B * ‖v‖ ^ (n + 1) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have habs : |(1 - t)^n| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _)]
      exact pow_le_one₀ (sub_nonneg.mpr ht.2) (sub_le_self 1 ht.1.le)
    have hop := (iteratedFDeriv ℝ (n + 1) u (x + t • v)).le_opNorm (fun _ => v)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hop
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |(1 - t)^n| * ‖iteratedFDeriv ℝ (n + 1) u (x + t • v) (fun _ => v)‖ ≤
          ‖iteratedFDeriv ℝ (n + 1) u (x + t • v) (fun _ => v)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) habs
      _ ≤ ‖iteratedFDeriv ℝ (n + 1) u (x + t • v)‖ * ‖v‖ ^ (n + 1) := hop
      _ ≤ B * ‖v‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (hB t ht') (pow_nonneg (norm_nonneg v) _)
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simp only [sub_zero, abs_one, mul_one] at hInt
  have h := mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr (Nat.cast_nonneg n.factorial))
  convert h using 1
  ring

end

end GlobalEmbedding.Offline
