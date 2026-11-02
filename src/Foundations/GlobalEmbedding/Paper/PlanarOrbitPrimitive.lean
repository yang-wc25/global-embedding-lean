import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import GlobalEmbedding.Paper.MatrixManifoldCompactParameterIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# The genuine period-one orbit primitive

Source: `literature/parallelizable-stable-plus-one/main.tex`, notation at226–232.
The primitive is the literal weighted integral, not an assumed antiderivative.
-/

open Set MeasureTheory
open scoped Topology ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The literal intrinsic weighted period integral from the paper. -/
noncomputable def planarOrbitPrimitive {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ → Q → Q) (u : Q → E) (z : Q) : E :=
  ∫ t in (0 : ℝ)..1, t • u (R t z)

/-- The genuine translated weighted integral differentiates to f minus its
period average. Native FTC and integration by parts prove the identity using
only continuity of the actual period-one orbit function. -/
theorem planarPeriodicPrimitive_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f)
    (hp : Function.Periodic f 1) (s : ℝ) :
    HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..1, t • f (t + y))
      (f s - ∫ t in (0 : ℝ)..1, f t) s := by
  let F : ℝ → E := fun y ↦ ∫ t in (0 : ℝ)..y, f t
  have hF (y : ℝ) : HasDerivAt F (f y) y :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hFdiff : Differentiable ℝ F := fun y ↦ (hF y).differentiableAt
  have hFc : Continuous F := hFdiff.continuous
  have hrep (y : ℝ) : (∫ t in (0 : ℝ)..1, t • f (t + y)) =
      F (1 + y) - ∫ t in y..1 + y, F t := by
    have hv : Continuous (fun t ↦ F (t + y)) := hFc.comp (continuous_id.add_const y)
    have hv' : Continuous (fun t ↦ f (t + y)) := hf.comp (continuous_id.add_const y)
    have hi := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
      (u := fun t : ℝ ↦ t) (v := fun t : ℝ ↦ F (t + y))
      (u' := fun _ ↦ (1 : ℝ)) (v' := fun t ↦ f (t + y))
      (a := 0) (b := 1) continuous_id.continuousOn hv.continuousOn
      (fun t _ ↦ hasDerivAt_id t)
      (fun t _ ↦ by simpa only [Function.comp_def, id_eq, one_smul] using (hF (t + y)).scomp t ((hasDerivAt_id t).add_const y))
      (continuous_const.intervalIntegrable 0 1) (hv'.intervalIntegrable 0 1)
    simpa only [one_smul, zero_smul, sub_zero, intervalIntegral.integral_comp_add_right,
      zero_add] using hi
  have hper : F (1 + s) - F s = ∫ t in (0 : ℝ)..1, f t := by
    change (∫ t in (0 : ℝ)..1 + s, f t) - (∫ t in (0 : ℝ)..s, f t) = _
    rw [intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    simpa only [add_comm 1 s, zero_add] using hp.intervalIntegral_add_eq s 0
  let G : ℝ → E := fun y ↦ ∫ t in (0 : ℝ)..y, F t
  have hG (y : ℝ) : HasDerivAt G (F y) y :=
    intervalIntegral.integral_hasDerivAt_right (hFc.intervalIntegrable _ _)
      hFc.aestronglyMeasurable.stronglyMeasurableAtFilter hFc.continuousAt
  have hrep' : (fun y ↦ ∫ t in (0 : ℝ)..1, t • f (t + y)) =
      fun y ↦ F (1 + y) - (G (1 + y) - G y) := by
    funext y
    rw [hrep]
    rw [← intervalIntegral.integral_interval_sub_left
      (hFc.intervalIntegrable 0 (1 + y)) (hFc.intervalIntegrable 0 y)]
  rw [hrep']
  have hFd : HasDerivAt (fun y ↦ F (1 + y)) (f (1 + s)) s := by
    simpa only [Function.comp_def, id_eq, one_smul] using (hF (1 + s)).scomp s ((hasDerivAt_id s).const_add 1)
  have hGd : HasDerivAt (fun y ↦ G (1 + y)) (F (1 + s)) s := by
    simpa only [Function.comp_def, id_eq, one_smul] using (hG (1 + s)).scomp s ((hasDerivAt_id s).const_add 1)
  have hd := hFd.sub (hGd.sub (hG s))
  rw [hper, add_comm 1 s, hp] at hd
  exact hd

/-- The actual intrinsic primitive has exactly the true orbit derivative u
minus its actual average, at every point with a continuous orbit observable. -/
theorem planarOrbitPrimitive_orbitDeriv {Q E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (u : Q → E) (z : Q)
    (hu : Continuous (fun t : ℝ ↦ u (R t z))) :
    orbitDeriv R (planarOrbitPrimitive R u) z = u z - orbitAverage R u z := by
  have heq : (fun y ↦ planarOrbitPrimitive R u (R y z)) =
      fun y ↦ ∫ t in (0 : ℝ)..1, t • u (R (t + y) z) := by
    funext y
    simp only [planarOrbitPrimitive, hadd]
  have hd := planarPeriodicPrimitive_hasDerivAt (fun t ↦ u (R t z)) hu
    (orbitMap_periodic R hadd hone u z) 0
  unfold orbitDeriv
  rw [heq]
  simpa only [hzero, orbitAverage] using hd.deriv

/-- On an actual zero-average input the displayed integral is genuinely a
primitive for the actual orbit derivative, with no supplied antiderivative. -/
theorem planarOrbitPrimitive_orbitDeriv_of_average_zero {Q E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (u : Q → E) (z : Q)
    (hu : Continuous (fun t : ℝ ↦ u (R t z))) (havg : orbitAverage R u z = 0) :
    orbitDeriv R (planarOrbitPrimitive R u) z = u z := by
  rw [planarOrbitPrimitive_orbitDeriv R hzero hadd hone u z hu, havg, sub_zero]

/-- The literal weighted primitive has zero mean when the original actual
periodic function has zero mean. Native compact Fubini exchanges the two actual
period integrals; periodicity makes the inner translated average vanish. -/
theorem planarPeriodicPrimitive_average_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f)
    (hp : Function.Periodic f 1) (havg : (∫ t in (0 : ℝ)..1, f t) = 0) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, t • f (t + s)) = 0 := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ p.2 • f (p.2 + p.1)) :=
    continuous_snd.smul (hf.comp (continuous_snd.add continuous_fst))
  have hi : IntegrableOn (fun p : ℝ × ℝ ↦ p.2 • f (p.2 + p.1))
      (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
    apply (hc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
    simp only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  rw [intervalIntegral_intervalIntegral_swap (F := fun s t : ℝ ↦ t • f (t + s))
    (a := 0) (b := 1) (c := 0) (d := 1) hi]
  have hinner (t : ℝ) : (∫ s in (0 : ℝ)..1, t • f (t + s)) = 0 := by
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_comp_add_left]
    have ht := hp.intervalIntegral_add_eq t 0
    simp only [zero_add] at ht
    rw [add_zero, ht, havg, smul_zero]
  simp only [hinner, intervalIntegral.integral_zero]

/-- Averaging the genuine zero-mean orbit primitive gives zero on that orbit. -/
theorem planarOrbitPrimitive_average_zero {Q E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (u : Q → E) (z : Q) (hu : Continuous (fun t : ℝ ↦ u (R t z)))
    (havg : orbitAverage R u z = 0) : orbitAverage R (planarOrbitPrimitive R u) z = 0 := by
  unfold orbitAverage planarOrbitPrimitive
  simp_rw [← hadd]
  exact planarPeriodicPrimitive_average_zero (fun t ↦ u (R t z)) hu
    (orbitMap_periodic R hadd hone u z) havg

/-- The genuine weighted orbit integral is smooth on the original ordinary
finite-dimensional native manifold. This directly reuses the accepted all-order
compact parameter integral, with the literal interval/Icc identification. -/
theorem planarOrbitPrimitive_contMDiff
    {P M E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(ℝ, P) ∞ M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) ∞
      (fun p : M × ℝ ↦ R p.2 p.1)) (u : M → E)
    (hu : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ u) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ (planarOrbitPrimitive R u) := by
  have hF : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : M × ℝ ↦ p.2 • u (R p.2 p.1)) :=
    contMDiff_snd.smul (hu.comp hR)
  have hI := contMDiff_compact_parameter_integral (⊤ : ℕ∞) _ hF
  apply hI.congr
  intro z
  unfold planarOrbitPrimitive
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Icc_eq_integral_Ioc]

#print axioms planarOrbitPrimitive_orbitDeriv
#print axioms planarOrbitPrimitive_average_zero
#print axioms planarOrbitPrimitive_contMDiff
#print axioms planarPeriodicPrimitive_hasDerivAt

end GlobalEmbedding.Paper
