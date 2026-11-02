import GlobalEmbedding.Paper.CollarCKTaylorHomogeneousPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Actual coordinate derivatives of the shared Taylor coefficients

Source: Gantumur, notes2, Theorem 18, coefficient differentiation and rational identities.
All coefficients use the accepted `collarCKTaylorCoeff` word fibers without rescaling.
The scalar formal package is the literal function `d ↦ collarCKTaylorCoeff p d`.
-/

namespace GlobalEmbedding.Paper

open scoped Topology
open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Native polynomial partial differentiation is actual coordinate Fréchet differentiation.
Use the existing analytic polynomial evaluation theorem for differentiability, and the
native polynomial induction/product rule for the exact coordinate formula. -/
theorem collarCKPolynomial_partial (P : MvPolynomial σ ℝ) (z : σ → ℝ) (i : σ) :
    fderiv ℝ (fun y ↦ MvPolynomial.eval y P) z (Pi.single i 1) =
      MvPolynomial.eval z (MvPolynomial.pderiv i P) := by
  have hd (Q : MvPolynomial σ ℝ) : DifferentiableAt ℝ (fun y ↦ MvPolynomial.eval y Q) z :=
    (AnalyticOnNhd.eval_mvPolynomial Q z (Set.mem_univ z)).differentiableAt
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    simp only [map_add]
    rw [fderiv_fun_add (hd P) (hd Q), add_apply, hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X, map_add]
    rw [fderiv_fun_mul (hd P) (differentiableAt_apply j z)]
    have hproj : fderiv ℝ (fun y : σ → ℝ ↦ y j) z = ContinuousLinearMap.proj j :=
      (ContinuousLinearMap.proj j : (σ → ℝ) →L[ℝ] ℝ).fderiv
    rw [hproj]
    by_cases hji : j = i <;> simp [hP, hji, mul_comm, add_comm]

omit [DecidableEq σ] in
/-- The nth native derivative-series coefficient uses only the next original coefficient. -/
theorem collarCKDerivSeries_congr (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (k : ℕ) (h : p (k + 1) = q (k + 1)) : p.derivSeries k = q.derivSeries k := by
  have h' : p (1 + k) = q (1 + k) := by
    rw [Nat.add_comm 1 k]
    exact h
  simp only [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.changeOriginSeries, FormalMultilinearSeries.changeOriginSeriesTerm,
    h']

omit [DecidableEq σ] in
/-- Differentiate a genuine homogeneous term using the native finite-series derivative
theorem. A temporary one-term multilinear series isolates the required coefficient;
no word-insertion or permutation formula is reproved. -/
theorem collarCKDerivSeries_diagonal (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (k : ℕ) (z : σ → ℝ) :
    fderiv ℝ (fun y ↦ p (k + 1) (fun _ ↦ y)) z = p.derivSeries k (fun _ ↦ z) := by
  classical
  let Q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ := Function.update 0 (k + 1) (p (k + 1))
  have hQ (m : ℕ) (hm : m ≠ k + 1) : Q m = 0 := by simp [Q, hm]
  have hQk : Q (k + 1) = p (k + 1) := by simp [Q]
  have hfinite (m : ℕ) (hm : k + 2 ≤ m) : Q m = 0 := hQ m (by omega)
  have hsum : Q.sum = fun y ↦ p (k + 1) (fun _ ↦ y) := by
    funext y
    change (∑' m, Q m (fun _ ↦ y)) = _
    rw [tsum_eq_single (k + 1) (fun m hm ↦ by rw [hQ m hm]; rfl), hQk]
  have hD (m : ℕ) (hm : m ≠ k) : Q.derivSeries m = 0 :=
    Q.derivSeries_eq_zero (hQ (m + 1) (by omega))
  have heq : Q.derivSeries k = p.derivSeries k := collarCKDerivSeries_congr Q p k hQk
  have hball := (Q.hasFiniteFPowerSeriesOnBall_of_finite hfinite).toHasFPowerSeriesOnBall
  have hs := hball.fderiv.hasSum (y := z) (by simp)
  have hs' : HasSum (fun m ↦ Q.derivSeries m (fun _ ↦ z))
      (Q.derivSeries k (fun _ ↦ z)) := by
    apply hasSum_single k
    intro m hm
    rw [hD m hm]
    rfl
  have hv := hs.unique hs'
  simpa only [zero_add, hsum, heq] using hv

/-- A genuine expansion of an actual coordinate derivative has the native shifted
coefficient formula. Native finite homogeneous polynomials avoid a second word-count proof. -/
theorem collarCKTaylorCoeff_analytic_partial (f : (σ → ℝ) → ℝ)
    (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (i : σ)
    (hq : HasFPowerSeriesAt (fun z ↦ fderiv ℝ f z (Pi.single i 1)) q 0)
    (d : σ →₀ ℕ) :
    collarCKTaylorCoeff q d =
      collarCKTaylorCoeff p (d + Finsupp.single i 1) * (d i + 1 : ℝ) := by
  let L : ((σ → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ) : σ → ℝ)
  let r := L.compFormalMultilinearSeries p.derivSeries
  obtain ⟨ρ, hball⟩ := hp
  have hr : HasFPowerSeriesAt (fun z ↦ fderiv ℝ f z (Pi.single i 1)) r 0 :=
    (L.comp_hasFPowerSeriesOnBall hball.fderiv).hasFPowerSeriesAt
  let P (s : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (k : ℕ) : MvPolynomial σ ℝ :=
    truncFinset ℝ (Finset.univ.image (collarCKWordIndex (σ := σ) (k := k)))
      (fun a ↦ collarCKTaylorCoeff s a : MvPowerSeries σ ℝ)
  have hpoly (k : ℕ) : P r k = MvPolynomial.pderiv i (P p (k + 1)) := by
    apply MvPolynomial.funext
    intro z
    calc
      MvPolynomial.eval z (P r k) = r k (fun _ ↦ z) :=
        collarCKTaylorHomogeneous_eval r k z
      _ = p.derivSeries k (fun _ ↦ z) (Pi.single i 1) := by
        rfl
      _ = fderiv ℝ (fun y ↦ p (k + 1) (fun _ ↦ y)) z (Pi.single i 1) :=
        congrArg (fun T : (σ → ℝ) →L[ℝ] ℝ ↦ T (Pi.single i 1))
          (collarCKDerivSeries_diagonal p k z).symm
      _ = MvPolynomial.eval z (MvPolynomial.pderiv i (P p (k + 1))) := by
        rw [← collarCKPolynomial_partial]
        have hfun : (fun y ↦ MvPolynomial.eval y (P p (k + 1))) =
            (fun y ↦ p (k + 1) (fun _ ↦ y)) :=
          funext (collarCKTaylorHomogeneous_eval p (k + 1))
        exact congrArg (fun h : (σ → ℝ) → ℝ ↦ fderiv ℝ h z (Pi.single i 1)) hfun.symm
  have hd : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    simp only [map_add, Finsupp.degree_single]
  calc
    collarCKTaylorCoeff q d = collarCKTaylorCoeff r d :=
      collarCKTaylorCoeff_unique _ q r hq hr d
    _ = (P r d.degree).coeff d := by
      symm
      simpa only [ite_true] using collarCKTaylorHomogeneous_coeff r d.degree d
    _ = (MvPolynomial.pderiv i (P p (d.degree + 1))).coeff d :=
      congrArg (fun Q : MvPolynomial σ ℝ ↦ Q.coeff d) (hpoly d.degree)
    _ = (P p (d.degree + 1)).coeff (d + Finsupp.single i 1) * (d i + 1 : ℝ) :=
      MvPolynomial.coeff_pderiv _ _
    _ = collarCKTaylorCoeff p (d + Finsupp.single i 1) * (d i + 1 : ℝ) := by
      congr 1
      have hc := collarCKTaylorHomogeneous_coeff p (d.degree + 1)
        (d + Finsupp.single i 1)
      rw [ite_eq_left hd] at hc
      exact hc

/-- Actual coordinate Fréchet partial differentiation becomes native formal `pderiv` on
the literal shared coefficient package, for any genuine input and output witnesses. -/
theorem collarCKTaylorPackage_partial (f : (σ → ℝ) → ℝ)
    (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (i : σ)
    (hq : HasFPowerSeriesAt (fun z ↦ fderiv ℝ f z (Pi.single i 1)) q 0) :
    (fun d ↦ collarCKTaylorCoeff q d : MvPowerSeries σ ℝ) =
      pderiv i (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries σ ℝ) := by
  apply MvPowerSeries.ext
  intro d
  exact (collarCKTaylorCoeff_analytic_partial f p q hp i hq d).trans
    (MvPowerSeries.coeff_pderiv
      (fun a ↦ collarCKTaylorCoeff p a : MvPowerSeries σ ℝ) d).symm

end GlobalEmbedding.Paper
