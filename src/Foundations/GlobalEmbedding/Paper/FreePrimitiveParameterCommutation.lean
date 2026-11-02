import GlobalEmbedding.Paper.PlanarOrbitPrimitive
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import GlobalEmbedding.Paper.MatrixCompactPeriodDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual parameter differentiation of the orbit average and weighted primitive

Source: `main.tex`, `thm:free`, lines431–475.
DAG: `free-primitive-parameter-commutation`; exclusive owner W2.
The accepted compact-period derivative theorem supplies differentiation through
the actual integral; the actual commuting flow law supplies the parameter identity.
-/

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Differentiating the genuine weighted period integral along a commuting old
flow gives the genuine weighted integral of the actual old orbit derivative.
The weight is fixed in the old parameter; no zero-average hypothesis is needed. -/
theorem free_weighted_period_orbitDeriv_comm
    (R S : PeriodOneSmoothFlow I M)
    (hcomm : ∀ t s z, R.flow t (S.flow s z) = S.flow s (R.flow t z))
    (h : M → F) (hh : ContMDiff I 𝓘(ℝ, F) ∞ h)
    (w : ℝ → ℝ) (hw : Continuous w) (z : M) :
    orbitDeriv S.flow
      (fun x ↦ ∫ t in Icc (0 : ℝ) 1, w t • h (R.flow t x)) z =
        ∫ t in Icc (0 : ℝ) 1, w t • orbitDeriv S.flow h (R.flow t z) := by
  let L : F →L[ℝ] (ℝ →L[ℝ] F) :=
    ContinuousLinearMap.smulRightL ℝ ℝ F (ContinuousLinearMap.id ℝ ℝ)
  let f : ℝ × ℝ → F := fun p ↦ w p.2 • h (S.flow p.1 (R.flow p.2 z))
  let g : ℝ × ℝ → ℝ →L[ℝ] F := fun p ↦
    L (w p.2 • orbitDeriv S.flow h (S.flow p.1 (R.flow p.2 z)))
  have hRz : Continuous (fun p : ℝ × ℝ ↦ R.flow p.2 z) :=
    R.smooth.continuous.comp (continuous_snd.prodMk continuous_const)
  have hSR : Continuous (fun p : ℝ × ℝ ↦ S.flow p.1 (R.flow p.2 z)) :=
    S.smooth.continuous.comp (continuous_fst.prodMk hRz)
  have hf : Continuous f := (hw.comp continuous_snd).smul (hh.continuous.comp hSR)
  have hdh := contMDiff_orbitDeriv S.flow S.smooth h hh
  have hg : Continuous g :=
    L.continuous.comp ((hw.comp continuous_snd).smul (hdh.continuous.comp hSR))
  have hd (a t : ℝ) : HasFDerivAt (fun b ↦ f (b, t)) (g (a, t)) a := by
    exact ((hasDerivAt_orbit S.flow S.smooth S.flow_add h hh a (R.flow t z)).const_smul
      (w t)).hasFDerivAt
  have hi := hasFDerivAt_compact_period f g hf hg hd (0 : ℝ)
  let k : ℝ → F := fun t ↦ w t • orbitDeriv S.flow h (R.flow t z)
  have hk : Continuous k := hw.smul
    (hdh.continuous.comp (R.smooth.continuous.comp
      (continuous_id.prodMk continuous_const)))
  have hgzero : (fun t ↦ g (0, t)) = fun t ↦ L (k t) := by
    funext t
    simp only [g, k, S.flow_zero]
  have heval : (∫ t in Icc (0 : ℝ) 1, g (0, t)) (1 : ℝ) =
      ∫ t in Icc (0 : ℝ) 1, k t := by
    rw [hgzero, L.integral_comp_comm
      (hk.continuousOn.integrableOn_Icc)]
    change (1 : ℝ) • (∫ t in Icc (0 : ℝ) 1, k t) = _
    exact one_smul ℝ _
  have hder : HasDerivAt (fun b ↦ ∫ t in Icc (0 : ℝ) 1, f (b, t))
      (∫ t in Icc (0 : ℝ) 1, k t) 0 := by
    rw [← heval]
    exact hi.hasDerivAt
  have heq : (fun b ↦ ∫ t in Icc (0 : ℝ) 1, w t • h (R.flow t (S.flow b z))) =
      (fun b ↦ ∫ t in Icc (0 : ℝ) 1, f (b, t)) := by
    funext b
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t ↦ congrArg (fun x ↦ w t • h x) (hcomm t b z)
  unfold orbitDeriv
  rw [heq]
  exact hder.deriv

/-- Actual old-factor differentiation commutes with the literal new-orbit average. -/
theorem free_orbitAverage_orbitDeriv_comm
    (R S : PeriodOneSmoothFlow I M)
    (hcomm : ∀ t s z, R.flow t (S.flow s z) = S.flow s (R.flow t z))
    (h : M → F) (hh : ContMDiff I 𝓘(ℝ, F) ∞ h) (z : M) :
    orbitDeriv S.flow (orbitAverage R.flow h) z =
      orbitAverage R.flow (orbitDeriv S.flow h) z := by
  change orbitDeriv S.flow (fun x ↦ orbitAverage R.flow h x) z = _
  simpa only [orbitAverage, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc, one_smul] using
    free_weighted_period_orbitDeriv_comm R S hcomm h hh (fun _ ↦ 1) continuous_const z

/-- Actual old-factor differentiation commutes with the literal weighted new-orbit primitive. -/
theorem free_orbitPrimitive_orbitDeriv_comm
    (R S : PeriodOneSmoothFlow I M)
    (hcomm : ∀ t s z, R.flow t (S.flow s z) = S.flow s (R.flow t z))
    (h : M → F) (hh : ContMDiff I 𝓘(ℝ, F) ∞ h) (z : M) :
    orbitDeriv S.flow (planarOrbitPrimitive R.flow h) z =
      planarOrbitPrimitive R.flow (orbitDeriv S.flow h) z := by
  change orbitDeriv S.flow (fun x ↦ planarOrbitPrimitive R.flow h x) z = _
  simpa only [planarOrbitPrimitive,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc, id_eq] using
    free_weighted_period_orbitDeriv_comm R S hcomm h hh id continuous_id z

/-- The actual old derivative of an everywhere zero-new-average observable again
has zero new average. This is the mean-zero input needed for the last primitive
in the original second-order cancellation. -/
theorem free_orbitAverage_orbitDeriv_zero
    (R S : PeriodOneSmoothFlow I M)
    (hcomm : ∀ t s z, R.flow t (S.flow s z) = S.flow s (R.flow t z))
    (h : M → F) (hh : ContMDiff I 𝓘(ℝ, F) ∞ h)
    (hmean : ∀ x, orbitAverage R.flow h x = 0) (z : M) :
    orbitAverage R.flow (orbitDeriv S.flow h) z = 0 := by
  rw [← free_orbitAverage_orbitDeriv_comm R S hcomm h hh z]
  unfold orbitDeriv
  simp only [hmean, deriv_const]

end GlobalEmbedding.Paper
