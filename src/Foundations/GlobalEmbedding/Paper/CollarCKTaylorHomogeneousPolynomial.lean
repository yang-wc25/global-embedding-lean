import GlobalEmbedding.Paper.CollarCKGoursatTaylorPositive
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Homogeneous polynomials of the shared commutative Taylor coefficients

Source: Gantumur, notes2, Theorem 18, coefficient differentiation and rational identities.
All coefficients use the accepted `collarCKTaylorCoeff` word fibers without rescaling.
The scalar formal package is the literal function `d ↦ collarCKTaylorCoeff p d`.
-/

namespace GlobalEmbedding.Paper

open scoped Topology
open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The same finite word fibers preserve addition of actual expansion coefficients. -/
theorem collarCKTaylorCoeff_add
    (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (d : σ →₀ ℕ) :
    collarCKTaylorCoeff (p + q) d = collarCKTaylorCoeff p d + collarCKTaylorCoeff q d := by
  simp only [collarCKTaylorCoeff, FormalMultilinearSeries.add_apply,
    add_apply, Finset.sum_add_distrib]

/-- The same finite word fibers preserve scalar multiplication, without a factorial change. -/
theorem collarCKTaylorCoeff_smul (a : ℝ)
    (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (d : σ →₀ ℕ) :
    collarCKTaylorCoeff (a • p) d = a • collarCKTaylorCoeff p d := by
  simp only [collarCKTaylorCoeff, FormalMultilinearSeries.smul_apply,
    smul_apply, Finset.smul_sum]

/-- The actual shared commutative formal packages preserve addition. -/
theorem collarCKTaylorPackage_add (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) :
    (fun d ↦ collarCKTaylorCoeff (p + q) d : MvPowerSeries σ ℝ) =
      (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries σ ℝ) +
        (fun d ↦ collarCKTaylorCoeff q d : MvPowerSeries σ ℝ) := by
  ext d
  exact collarCKTaylorCoeff_add p q d

/-- The shared commutative coefficient is independent of a genuine nonsymmetric expansion
witness. Reuse the accepted intrinsic derivative formula and cancel the positive factorial. -/
theorem collarCKTaylorCoeff_unique (f : (σ → ℝ) → ℝ)
    (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt f q 0) (d : σ →₀ ℕ) :
    collarCKTaylorCoeff p d = collarCKTaylorCoeff q d := by
  have h : (d.degree.factorial : ℝ) * collarCKTaylorCoeff p d =
      (d.degree.factorial : ℝ) * collarCKTaylorCoeff q d := by
    rw [collarCKTaylorCoeff_factorial f p hp, collarCKTaylorCoeff_factorial f q hq]
  exact mul_left_cancel₀ (by positivity : (d.degree.factorial : ℝ) ≠ 0) h

/-- Equal actual analytic germs have the same shared coefficients, without assuming that
their nonsymmetric multilinear witnesses are equal. -/
theorem collarCKTaylorCoeff_congr (f g : (σ → ℝ) → ℝ)
    (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0)
    (hfg : f =ᶠ[𝓝 0] g) (d : σ →₀ ℕ) :
    collarCKTaylorCoeff p d = collarCKTaylorCoeff q d :=
  collarCKTaylorCoeff_unique g p q (hp.congr hfg) hq d

/-- Actual analytic addition gives the native coefficient sum for any genuine output witness. -/
theorem collarCKTaylorCoeff_analytic_add (f g : (σ → ℝ) → ℝ)
    (p q r : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0)
    (hr : HasFPowerSeriesAt (f + g) r 0) (d : σ →₀ ℕ) :
    collarCKTaylorCoeff r d = collarCKTaylorCoeff p d + collarCKTaylorCoeff q d :=
  (collarCKTaylorCoeff_unique (f + g) r (p + q) hr (hp.add hq) d).trans
    (collarCKTaylorCoeff_add p q d)

/-- Actual analytic scalar multiplication gives the native scaled coefficients. -/
theorem collarCKTaylorCoeff_analytic_smul (a : ℝ) (f : (σ → ℝ) → ℝ)
    (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt (a • f) q 0) (d : σ →₀ ℕ) :
    collarCKTaylorCoeff q d = a • collarCKTaylorCoeff p d :=
  (collarCKTaylorCoeff_unique (a • f) q (a • p) hq (hp.const_smul (c := a)) d).trans
    (collarCKTaylorCoeff_smul a p d)

/-- A native polynomial truncation of one word degree retains exactly that homogeneous
part of the same shared coefficient package. No new Taylor coefficient object is defined. -/
theorem collarCKTaylorHomogeneous_coeff (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (k : ℕ) (d : σ →₀ ℕ) :
    (truncFinset ℝ (Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)))
      (fun a ↦ collarCKTaylorCoeff p a : MvPowerSeries σ ℝ)).coeff d =
        if d.degree = k then collarCKTaylorCoeff p d else 0 := by
  classical
  let P : MvPowerSeries σ ℝ := fun a ↦ collarCKTaylorCoeff p a
  change (truncFinset ℝ _ P).coeff d = _
  rw [coeff_truncFinset]
  by_cases hd : d.degree = k
  · subst k
    by_cases hm : d ∈ Finset.univ.image (collarCKWordIndex (σ := σ) (k := d.degree))
    · simp only [hm, ite_true]
      exact coeff_apply P d
    · have hz : collarCKTaylorCoeff p d = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        exact False.elim (hm (Finset.mem_image.mpr
          ⟨w, Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩))
      simp only [hm, ite_false, ite_true, hz]
  · have hm : d ∉ Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)) := by
      rintro h
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
      exact hd (collarCKWordIndex_degree w)
    simp only [hd, hm, ite_false]

/-- The native finite polynomial for a homogeneous degree evaluates to the genuine
homogeneous multilinear term, by the already accepted exact word-fiber representation. -/
theorem collarCKTaylorHomogeneous_eval (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (k : ℕ) (z : σ → ℝ) :
    MvPolynomial.eval z
      (truncFinset ℝ (Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)))
        (fun a ↦ collarCKTaylorCoeff p a : MvPowerSeries σ ℝ)) = p k (fun _ ↦ z) := by
  let P : MvPowerSeries σ ℝ := fun a ↦ collarCKTaylorCoeff p a
  change MvPolynomial.eval z (truncFinset ℝ _ P) = _
  rw [truncFinset_apply, collarCKTaylorCoeff_homogeneous p k z]
  simp only [map_sum, MvPolynomial.eval_monomial, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d _
  exact mul_comm _ _

end GlobalEmbedding.Paper
