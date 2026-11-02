import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Actual weighted period Gram matrices are positive definite

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line307.
DAG node: `matrix-weighted-period-gram-positive`.
-/

open Set Filter MeasureTheory
open scoped BigOperators Matrix

namespace GlobalEmbedding.Paper

/-- Actual continuous independent period functions give an actual positive definite
weighted period-integral Gram matrix when the actual weight is nonnegative and
positive almost everywhere.

Proof: finite integral linearity identifies its actual quadratic form with the
actual integral of ρ times the squared linear combination. This integral is
nonnegative; if zero, native nonnegative-integral rigidity and positivity of ρ
make the actual combination zero almost everywhere. Native continuity/ae equality
on a nondegenerate closed real interval makes it zero everywhere on the period.
Actual linear independence forces every coefficient zero. Symmetry is pointwise
commutativity of the actual integrand. Source: `prop:matrix`, line307. -/
theorem weighted_period_gram_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Continuous (f i))
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hρnonneg : ∀ t, 0 ≤ ρ t)
    (hρpos : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), 0 < ρ t)
    (hindep : LinearIndependent ℝ
      (fun i ↦ fun t : Icc (0 : ℝ) 1 ↦ f i t.val)) :
    Matrix.PosDef (fun i j ↦ ∫ t in Icc (0 : ℝ) 1, ρ t * f i t * f j t) := by
  let G : Matrix ι ι ℝ := fun i j ↦ ∫ t in Icc (0 : ℝ) 1, ρ t * f i t * f j t
  have hsym : G.IsHermitian := by
    ext i j
    change star (∫ t in Icc (0 : ℝ) 1, ρ t * f j t * f i t) =
      ∫ t in Icc (0 : ℝ) 1, ρ t * f i t * f j t
    rw [star_trivial]
    apply integral_congr_ae
    filter_upwards with t
    ring
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro c hc
  let S : ℝ → ℝ := fun t ↦ ∑ i, c i * f i t
  have hS : Continuous S := by dsimp only [S]; fun_prop
  have hprod : Continuous (fun t ↦ ρ t * S t ^ 2) := hρ.mul (hS.pow 2)
  have hnonneg (t : ℝ) : 0 ≤ ρ t * S t ^ 2 := mul_nonneg (hρnonneg t) (sq_nonneg _)
  have hquad : star c ⬝ᵥ (G *ᵥ c) = ∫ t in Icc (0 : ℝ) 1, ρ t * S t ^ 2 := by
    have hexp : (fun t ↦ ρ t * S t ^ 2) =
        (fun t ↦ ∑ i, ∑ j, c i * (ρ t * f i t * f j t) * c j) := by
      funext t
      dsimp only [S]
      rw [pow_two]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hexp]
    have hterm (i j : ι) : Continuous (fun t ↦ c i * (ρ t * f i t * f j t) * c j) := by
      fun_prop
    have houter (i : ι) : Continuous (fun t ↦ ∑ j, c i * (ρ t * f i t * f j t) * c j) := by
      fun_prop
    rw [integral_finsetSum _ (fun i _ ↦ (houter i).continuousOn.integrableOn_Icc)]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ ↦ (hterm i j).continuousOn.integrableOn_Icc)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const, integral_const_mul]
    dsimp only [G]
    ring
  rw [hquad]
  apply lt_of_le_of_ne (integral_nonneg hnonneg)
  intro hzero
  have hazero : (fun t ↦ ρ t * S t ^ 2) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hprod.continuousOn.integrableOn_Icc).mp hzero.symm
  have hSzero : S =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 := by
    filter_upwards [hazero, hρpos] with t ht hpos
    have hs : S t ^ 2 = 0 := (mul_eq_zero.mp ht).resolve_left hpos.ne'
    exact (sq_eq_zero_iff.mp hs)
  have hEq : EqOn S 0 (Icc (0 : ℝ) 1) :=
    Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hSzero hS.continuousOn continuousOn_const
  have hsum : ∑ i, c i • (fun t : Icc (0 : ℝ) 1 ↦ f i t.val) = 0 := by
    funext t
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using hEq t.property
  exact hc (funext ((Fintype.linearIndependent_iff.mp hindep) c hsum))

#print axioms weighted_period_gram_positive

end GlobalEmbedding.Paper
