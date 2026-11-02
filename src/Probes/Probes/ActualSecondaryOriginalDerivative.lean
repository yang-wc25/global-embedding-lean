import Smoothing.ParameterRound2MeanPrimitives
import Probes.ActualIncrementPrimaryCoefficientBinding

/-! The literal primary derivative from original local primitive hypotheses.
The original binding treats inactive labels by their true zero germs. No phase
is required to be differentiable outside its primary domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem actual_grouped_real_derivative_smul
    {Label Slots : Type*} [Fintype Label] {N : ℕ}
    (theta : Label → ℝ) (a : Label → Slots → Fin N → ℂ) (delta : ℝ) (i : Slots) :
    incrementsGroupedRealDerivative theta (delta • a) i =
      delta • incrementsGroupedRealDerivative theta a i := by
  ext c
  change (∑ nu, (incrementsMeanPhase (theta nu) * (delta • a) nu i c).re) =
    delta * ∑ nu, (incrementsMeanPhase (theta nu) * a nu i c).re
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro nu hnu
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

 theorem actual_original_primary_grouped_derivative
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (q : ℕ) (hq : 1 ≤ q) (tau delta : ℝ) (htau : 0 < tau)
    (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
    (z : X) (hz : z.2 ∈ e.target) (hzW : (z.1,e.symm z.2) ∈ W) (i : Fin (m+1)) :
    let phi := fun nu t x => g.phase nu (t,e.symm x)
    let P := fun nu t beta x => delta •
      incrementsGlobalPrimaryExtension F hF g input (q+2) tau true nu beta (t,e.symm x)
    let Q := fun nu t beta x => delta •
      incrementsGlobalPrimaryExtension F hF g input (q+2) tau false nu beta (t,e.symm x)
    fderiv ℝ (fun x => actualPrimaryJointWave phi tau (fun _ _ _ _ => 1) P Q (z.1,x)) z.2
      (EuclideanSpace.single i 1) =
      incrementsGroupedRealDerivative (fun nu => phi nu z.1 z.2 / tau)
        (incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ _ _ => 1) P Q
          (fun r _ => EuclideanSpace.single r 1) z) i := by
  intro phi P Q
  have hb := increments_global_primary_mean_binding F hF g input q hq tau htau W h.hW primary
    h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse h.hCombinedSupport
    h.hPhase h.hCut h.hNormal h.hArgument h.hEta h.hPositive h.hUnit h.hPartition h.hSymm h.hDecomp
    h.hDouble h.hInteraction h.hG h.hJ h.hT0 h.hA h.hB h.hSecond
  have hd := (hb.2.2 e he heInv z.1 z.2 hz hzW).2.1 delta i
  have hc : incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ _ _ => 1) P Q
      (fun r _ => EuclideanSpace.single r 1) z =
      delta • incrementsGlobalObservedCoefficient F hF g input (q+2) tau e z.1 z.2 := by
    funext nu
    exact actual_original_primary_physical_coefficient_binding F hF g input (q+2) tau delta e z nu
  rw [hc, actual_grouped_real_derivative_smul]
  have hw := actual_original_primary_wave_physical_binding F hF g input (q+2) tau delta
    (fun w : X => (w.1,e.symm w.2))
  have hs := congrArg (fun U : X → V => fun x => U (z.1,x)) hw
  change (fun x => actualPrimaryJointWave phi tau (fun _ _ _ _ => 1) P Q (z.1,x)) = _ at hs
  rw [hs]
  exact hd

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_grouped_real_derivative_smul
#print axioms GlobalEmbedding.Continuation.actual_original_primary_grouped_derivative
