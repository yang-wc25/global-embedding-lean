import Mathlib.Analysis.Calculus.Deriv.Prod
import GlobalEmbedding.Paper.MatrixPeriodicAverageInvariance
import GlobalEmbedding.Paper.PlanarOrbitPrimitive
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import GlobalEmbedding.Paper.PlanarReflectionAreaZero
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Actual matrix orbit calculus on period-one flows

Source: `main.tex`, prop:matrix, lines 303–338. DAG: `matrix-orbit-matrix-calculus`.
All derivatives and averages below are the accepted actual period-one operations.
The literal primitive is the accepted weighted integral, not a supplied solver.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise
open MeasureTheory

namespace GlobalEmbedding.Paper

/-- The actual orbit average is invariant under the actual action. This is the
native periodic interval-integral translation identity on the same orbit. -/
theorem matrix_orbitAverage_invariant {Q E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ → Q → Q)
    (hadd : ∀ s t x, R (s + t) x = R s (R t x)) (hone : ∀ x, R 1 x = x)
    (u : Q → E) (x : Q) (a : ℝ) :
    orbitAverage R u (R a x) = orbitAverage R u x := by
  simpa only [orbitAverage,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    MeasureTheory.integral_Icc_eq_integral_Ioc] using
    periodic_average_invariant R hadd hone u x a

/-- An actual scalar observable odd under the half-action has zero actual mean.
Half-action invariance equals the negative mean by literal integration; over ℝ
that equality forces the mean to vanish. -/
theorem matrix_orbitAverage_half_odd_zero {Q : Type*} (R : ℝ → Q → Q)
    (hadd : ∀ s t x, R (s + t) x = R s (R t x)) (hone : ∀ x, R 1 x = x)
    (u : Q → ℝ) (hodd : ∀ x, u (R (1 / 2 : ℝ) x) = -u x) (x : Q) :
    orbitAverage R u x = 0 := by
  have hi := matrix_orbitAverage_invariant R hadd hone u x (1 / 2)
  have hn : orbitAverage R u (R (1 / 2 : ℝ) x) = -orbitAverage R u x := by
    unfold orbitAverage
    calc
      _ = ∫ t in (0 : ℝ)..1, -u (R t x) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [← hadd, add_comm t (1 / 2), hadd, hodd]
      _ = _ := intervalIntegral.integral_neg
  linarith

/-- Taking an actual matrix coefficient commutes with the actual orbit integral.
The finite coordinate evaluation is a real continuous linear map, so the native
Bochner integral commuting theorem applies to the actual continuous orbit. -/
theorem matrix_orbitAverage_apply {Q : Type*} {d : ℕ} (R : ℝ → Q → Q)
    (u : Q → Matrix (Fin d) (Fin d) ℝ) (x : Q)
    (hu : Continuous (fun t : ℝ ↦ u (R t x))) (i j : Fin d) :
    orbitAverage R u x i j = orbitAverage R (fun y ↦ u y i j) x := by
  let L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ Fin d → ℝ) i)
  exact (L.intervalIntegral_comp_comm (hu.intervalIntegrable 0 1)).symm

/-- Taking a coefficient commutes with the literal weighted primitive, by the
same genuine coordinate continuous linear map and its scalar linearity. -/
theorem matrix_primitive_apply {Q : Type*} {d : ℕ} (R : ℝ → Q → Q)
    (u : Q → Matrix (Fin d) (Fin d) ℝ) (x : Q)
    (hu : Continuous (fun t : ℝ ↦ u (R t x))) (i j : Fin d) :
    planarOrbitPrimitive R u x i j = planarOrbitPrimitive R (fun y ↦ u y i j) x := by
  let L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ Fin d → ℝ) i)
  have hh := (L.intervalIntegral_comp_comm (μ := volume)
    ((continuous_id.smul hu).intervalIntegrable 0 1)).symm
  change ((∫ t in (0 : ℝ)..1, t • u (R t x)) i j) =
    ∫ t in (0 : ℝ)..1, (t • u (R t x)) i j at hh
  exact hh

section Native
variable {P M : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace M] [ChartedSpace P M]
    [IsManifold 𝓘(ℝ, P) ∞ M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The average of the genuine derivative of a smooth native observable is zero.
The actual smooth derivative is integrable on the compact period; actual FTC and
the true period-one flow endpoints give zero, also for matrix-valued observables. -/
theorem matrix_orbitDeriv_average_zero (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (f : M → E) (hf : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ f) (x : M) :
    orbitAverage R.flow (orbitDeriv R.flow f) x = 0 := by
  have hv := contMDiff_orbitDeriv R.flow R.smooth f hf
  have hc : Continuous (fun t : ℝ ↦ orbitDeriv R.flow f (R.flow t x)) :=
    hv.continuous.comp (R.smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_orbit R.flow R.smooth R.flow_add f hf t x)
    (hc.intervalIntegrable 0 1)
  simpa only [orbitAverage, R.flow_one, R.flow_zero, sub_self] using hh

/-- The literal weighted primitive of the actual derivative is the observable
minus its actual average. Apply genuine vector-valued integration by parts to
u(t)=t and v(t)=f(R_t x); the period-one endpoint is f(x). -/
theorem matrix_primitive_orbitDeriv (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (f : M → E) (hf : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ f) (x : M) :
    planarOrbitPrimitive R.flow (orbitDeriv R.flow f) x = f x - orbitAverage R.flow f x := by
  have hc : Continuous (fun t : ℝ ↦ f (R.flow t x)) :=
    hf.continuous.comp (R.smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hv := contMDiff_orbitDeriv R.flow R.smooth f hf
  have hvc : Continuous (fun t : ℝ ↦ orbitDeriv R.flow f (R.flow t x)) :=
    hv.continuous.comp (R.smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hh := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) continuous_id.continuousOn hc.continuousOn
    (fun t _ ↦ hasDerivAt_id t)
    (fun t _ ↦ hasDerivAt_orbit R.flow R.smooth R.flow_add f hf t x)
    (continuous_const.intervalIntegrable 0 1) (hvc.intervalIntegrable 0 1)
  simpa only [planarOrbitPrimitive, orbitAverage, R.flow_one, R.flow_zero,
    id_eq, one_smul, zero_smul, sub_zero] using hh

set_option backward.isDefEq.respectTransparency false in
/-- The actual period matrix of any smooth matrix primitive is skew. Differentiate
its actual column scalar products along each orbit and use genuine periodic FTC.
This proves the entry relation directly for the literal matrix integral. -/
theorem matrix_primitive_period_skew {d : ℕ}
    (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (p : M → Matrix (Fin d) (Fin d) ℝ)
    (hp : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ p)
    (x : M) (i j : Fin d) :
    orbitAverage R.flow (fun y ↦ (p y).transpose * orbitDeriv R.flow p y) x i j =
      -orbitAverage R.flow (fun y ↦ (p y).transpose * orbitDeriv R.flow p y) x j i := by
  let q := orbitDeriv R.flow p
  have hq := contMDiff_orbitDeriv R.flow R.smooth p hp
  have hpc : Continuous (fun t : ℝ ↦ p (R.flow t x)) :=
    hp.continuous.comp (R.smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hqc : Continuous (fun t : ℝ ↦ q (R.flow t x)) :=
    hq.continuous.comp (R.smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hc (i j : Fin d) : Continuous
      (fun t : ℝ ↦ ((p (R.flow t x)).transpose * q (R.flow t x)) i j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact continuous_finsetSum _ (fun k _ ↦
      ((continuous_apply i).comp ((continuous_apply k).comp hpc)).mul
        ((continuous_apply j).comp ((continuous_apply k).comp hqc)))
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ ↦ ∑ k, p (R.flow t x) k i * p (R.flow t x) k j)
      (((p (R.flow t x)).transpose * q (R.flow t x)) i j +
        ((p (R.flow t x)).transpose * q (R.flow t x)) j i) t := by
    have hdp := hasDerivAt_orbit R.flow R.smooth R.flow_add p hp t x
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hdp k) i).mul
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp hdp k) j)))
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_add_distrib,
      Pi.mul_apply, mul_comm, add_comm, q] using hh
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ ↦ hd t)
    (((hc i j).add (hc j i)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add ((hc i j).intervalIntegrable 0 1)
    ((hc j i).intervalIntegrable 0 1)] at hh
  simp only [R.flow_one, R.flow_zero, sub_self] at hh
  have hmc : Continuous (fun t : ℝ ↦ (p (R.flow t x)).transpose * q (R.flow t x)) := by
    exact continuous_pi (fun i ↦ continuous_pi (fun j ↦ hc i j))
  rw [matrix_orbitAverage_apply R.flow _ x hmc i j,
    matrix_orbitAverage_apply R.flow _ x hmc j i]
  change (∫ t in (0 : ℝ)..1, ((p (R.flow t x)).transpose * q (R.flow t x)) i j) =
    -(∫ t in (0 : ℝ)..1, ((p (R.flow t x)).transpose * q (R.flow t x)) j i)
  linarith

end Native

#print axioms matrix_primitive_period_skew
#print axioms matrix_orbitAverage_apply
#print axioms matrix_primitive_apply
#print axioms matrix_orbitAverage_invariant
#print axioms matrix_orbitAverage_half_odd_zero
#print axioms matrix_orbitDeriv_average_zero
#print axioms matrix_primitive_orbitDeriv
end GlobalEmbedding.Paper
