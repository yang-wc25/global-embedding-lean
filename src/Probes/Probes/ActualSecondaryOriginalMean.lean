import Probes.ActualSecondaryOriginalDerivative
import Probes.ActualIncrementPrimaryCoefficientPrimitives

/-! The opposite-primary tensor in the literal finite metric identity is
exactly delta squared times the original native mean of the SAME amplitudes.
Every source direction is the true observation vector; all same-phase
subordinate cross terms remain in the original coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical ComplexConjugate
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_original_observed_opposite_mean
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (length : ℕ) (tau : ℝ) (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
    (z : X) (hz : z.2 ∈ e.target) (hzW : (z.1,e.symm z.2) ∈ W)
    (i j : Fin (m+1)) :
    (incrementsOppositePrimaryContribution
      (incrementsGlobalObservedCoefficient F hF g input length tau e z.1 z.2) i j).re =
    incrementsGlobalPrimaryMean F hF g input length tau z.1 (e.symm z.2)
      (incrementsGlobalObservationVector (I := I) e z.2 i)
      (incrementsGlobalObservationVector (I := I) e z.2 j) := by
  let coeff := incrementsGlobalObservedCoefficient F hF g input length tau e z.1 z.2
  let v := incrementsGlobalObservationVector (I := I) e z.2
  have hCoeffNative := actual_original_observed_coefficient_native_from_primitives F hF g input length tau
    W h.hW primary h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse
    h.hCombinedSupport h.hCut h.hNormal h.hArgument h.hEta h.hPositive h.hG h.hJ h.hT0 h.hA h.hB
    h.hSecond e he heInv z.1 z.2 hz hzW
  have hterm (nu : Λ) : ((1/4 : ℂ) *
      ((coeff nu i ⬝ᵥ (fun co => conj (coeff nu j co))) +
        ((fun co => conj (coeff nu i co)) ⬝ᵥ coeff nu j))).re =
      (1/2 : ℝ) *
        (inner ℝ (incrementsGlobalPrimaryCoefficient F hF g input length tau true nu
            (z.1,e.symm z.2) (v i))
          (incrementsGlobalPrimaryCoefficient F hF g input length tau true nu
            (z.1,e.symm z.2) (v j)) +
         inner ℝ (incrementsGlobalPrimaryCoefficient F hF g input length tau false nu
            (z.1,e.symm z.2) (v i))
          (incrementsGlobalPrimaryCoefficient F hF g input length tau false nu
            (z.1,e.symm z.2) (v j))) := by
    rw [show (1/4 : ℂ) = ((1/4 : ℝ) : ℂ) by norm_num]
    simp only [coeff,v,dotProduct,hCoeffNative,Complex.mul_re,Complex.add_re,
      Complex.mul_im,Complex.add_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.re_sum,Complex.im_sum,zero_mul,mul_zero,one_mul,zero_add,add_zero,sub_zero,
      PiLp.inner_apply,Real.inner_apply]
    ring_nf
    rw [Finset.sum_add_distrib]
    ring
  change (incrementsOppositePrimaryContribution coeff i j).re = _
  unfold incrementsOppositePrimaryContribution
  rw [Complex.re_sum]
  simp_rw [hterm]
  simp only [v,incrementsGlobalPrimaryMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul,Finset.mul_sum]

 theorem actual_original_primary_opposite_tensor
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (length : ℕ) (tau delta : ℝ) (e : OpenPartialHomeomorph M D)
    (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
    (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
    (z : X) (hz : z.2 ∈ e.target) (hzW : (z.1,e.symm z.2) ∈ W) :
    let phi := fun nu t x => g.phase nu (t,e.symm x)
    let P := fun nu t beta x => delta •
      incrementsGlobalPrimaryExtension F hF g input length tau true nu beta (t,e.symm x)
    let Q := fun nu t beta x => delta •
      incrementsGlobalPrimaryExtension F hF g input length tau false nu beta (t,e.symm x)
    actualPrimaryOppositeMeanTensor phi tau (fun _ _ _ _ => 1) P Q z =
      delta^2 • actualRealTensorAssembly (fun i j =>
        (incrementsGlobalPrimaryMean F hF g input length tau z.1 (e.symm z.2)
          (incrementsGlobalObservationVector (I := I) e z.2 i)
          (incrementsGlobalObservationVector (I := I) e z.2 j) : ℂ)) := by
  intro phi P Q
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  have hc : incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ _ _ => 1) P Q
      (fun r _ => EuclideanSpace.single r 1) z =
      delta • incrementsGlobalObservedCoefficient F hF g input length tau e z.1 z.2 := by
    funext nu
    exact actual_original_primary_physical_coefficient_binding F hF g input length tau delta e z nu
  simp only [actualPrimaryOppositeMeanTensor,actualRealTensorAssembly_basis,hc,
    incrementsOppositePrimaryContribution_smul,smul_apply,smul_eq_mul,Complex.ofReal_re]
  rw [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    actual_original_observed_opposite_mean F hF g input W primary h length tau e he heInv z hz hzW i j]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_observed_opposite_mean
#print axioms GlobalEmbedding.Continuation.actual_original_primary_opposite_tensor
