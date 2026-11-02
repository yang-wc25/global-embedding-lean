import GlobalEmbedding.Paper.CollarCKTaylorHomogeneousPolynomial
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The actual scalar coordinate has the native formal variable as its Taylor package

Source: Gantumur, notes2, Theorem 18, the coordinate variables in the Taylor equations.
Use the accepted shared word-fiber coefficients and native continuous linear expansion.
-/

namespace GlobalEmbedding.Paper

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A genuine expansion of the scalar coordinate function packages to the native variable.
Source: Gantumur, Theorem 18. The native continuous linear projection has only its degree-one
homogeneous term. The accepted homogeneous polynomial evaluation law identifies that term
with the coordinate polynomial and all other terms with zero. Taking coefficients identifies
the native package with `X i`. Accepted witness independence transfers this identity to any
genuine, possibly nonsymmetric multilinear expansion of the same scalar coordinate function. -/
theorem collarCKTaylorPackage_scalar_coordinate (i : σ)
    (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt (fun z : σ → ℝ ↦ z i) p 0) :
    (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries σ ℝ) = X i := by
  let L : (σ → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let q := L.fpowerSeries 0
  have hpoly (k : ℕ) :
      truncFinset ℝ (Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)))
        (fun d ↦ collarCKTaylorCoeff q d : MvPowerSeries σ ℝ) =
          if k = 1 then MvPolynomial.X i else 0 := by
    apply MvPolynomial.funext
    intro z
    rw [collarCKTaylorHomogeneous_eval]
    rcases k with _ | (_ | k)
    · simp [q]
    · simp [q, L]
    · simp [q]
  apply MvPowerSeries.ext
  intro d
  change collarCKTaylorCoeff p d = coeff d (X i : MvPowerSeries σ ℝ)
  rw [collarCKTaylorCoeff_unique (fun z : σ → ℝ ↦ z i) p q hp
    (L.hasFPowerSeriesAt 0)]
  have hc := collarCKTaylorHomogeneous_coeff q d.degree d
  rw [hpoly] at hc
  simp only [ite_true] at hc
  by_cases hd : d.degree = 1
  · simpa only [hd, ite_true, MvPolynomial.coeff_X, coeff_X, eq_comm] using hc.symm
  · have hn : d ≠ Finsupp.single i 1 := by
      intro h
      exact hd (h ▸ Finsupp.degree_single i 1)
    simpa [hd, coeff_X, hn] using hc.symm

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKTaylorPackage_scalar_coordinate
