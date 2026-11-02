import NormalPolar.ActualRepairModelFirstDefectCoordinates

/-! A genuine inverse source chart transports the total derivative even
when a phase or an amplitude is not differentiable. This removes global
smoothness assumptions on inactive phases from the common-array mean and
metric-remainder coordinate identities. No estimates are used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GlobalEmbedding.Continuation
variable {m d N count : ℕ} {M Label : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem actualRepairModelFirstDefect_inverse_derivative_total
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (f : M → Y) (y : D) (hy : y ∈ e.target) (v : D) :
    fderiv ℝ (f ∘ e.symm) y v =
      tangentSpaceCastModel 𝓘(ℝ,Y) (f (e.symm y))
        (mfderiv 𝓙 𝓘(ℝ,Y) f (e.symm y)
          (mfderiv 𝓘(ℝ,D) 𝓙 e.symm y ((tangentSpaceCastModel 𝓘(ℝ,D) y).symm v))) := by
  have hemd : e.MDifferentiable 𝓙 𝓘(ℝ,D) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  by_cases hf : MDifferentiableAt 𝓙 𝓘(ℝ,Y) f (e.symm y)
  · rw [← mfderiv_comp_apply y hf (hemd.mdifferentiableAt_symm hy),mfderiv_eq_fderiv]
    rfl
  · have hn : ¬ DifferentiableAt ℝ (f ∘ e.symm) y := by
      intro h
      have ho : MDifferentiableAt 𝓘(ℝ,D) 𝓘(ℝ,Y) (f ∘ e.symm) (e (e.symm y)) := by
        rw [e.right_inv hy]
        exact h.mdifferentiableAt
      have hcomp := ho.comp (e.symm y) (hemd.mdifferentiableAt (e.map_target hy))
      have heq : f =ᶠ[𝓝 (e.symm y)] ((f ∘ e.symm) ∘ e) := by
        filter_upwards [e.open_source.mem_nhds (e.map_target hy)] with x hx
        simp only [Function.comp_apply,e.left_inv hx]
      exact hf (hcomp.congr_of_eventuallyEq heq)
    rw [fderiv_zero_of_not_differentiableAt hn,mfderiv_zero_of_not_mdifferentiableAt hf]
    rfl

theorem actualRepairModelFirstDefect_observed_coefficient_total
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (phi : Ep × M → ℝ) (R Q : Ep × M → V) (tau : ℝ)
    (b : Ep) (x v : D) (hx : x ∈ e.target) (co : Fin N) :
    let w := mfderiv 𝓘(ℝ,D) 𝓙 e.symm x ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm v)
    incrementsPrimaryDerivativeCoefficient (fun y => phi (b,e.symm y)) tau
      (fun (_ : Unit) _ => 1) (fun _ y => R (b,e.symm y)) (fun _ y => Q (b,e.symm y)) x v co =
      (round4PrescribedNativeCoefficient (I := 𝓙) false phi tau R Q (b,e.symm x) w co : ℂ) +
      Complex.I * (round4PrescribedNativeCoefficient (I := 𝓙) true phi tau R Q (b,e.symm x) w co : ℂ) := by
  intro w
  have hr := actualRepairModelFirstDefect_inverse_derivative_total e he (fun y => R (b,y)) x hx v
  have hq := actualRepairModelFirstDefect_inverse_derivative_total e he (fun y => Q (b,y)) x hx v
  have hphi := actualRepairModelFirstDefect_inverse_derivative_total e he (fun y => phi (b,y)) x hx v
  simp only [Function.comp_def] at hr hq hphi
  simp only [incrementsPrimaryDerivativeCoefficient,Finset.univ_unique,Finset.sum_singleton,
    fderiv_const_apply,ContinuousLinearMap.zero_apply,Complex.ofReal_zero,mul_zero,zero_mul,
    one_mul,Complex.ofReal_one,zero_add]
  change _ =
    ((incrementsGlobalSpatialDerivative (I := 𝓙) R (b,e.symm x) w -
      incrementsGlobalScalarDerivative (I := 𝓙) phi (b,e.symm x) w • (tau⁻¹ • Q (b,e.symm x))) co : ℂ) +
    Complex.I * ((incrementsGlobalSpatialDerivative (I := 𝓙) Q (b,e.symm x) w +
      incrementsGlobalScalarDerivative (I := 𝓙) phi (b,e.symm x) w • (tau⁻¹ • R (b,e.symm x))) co : ℂ)
  rw [hr,hq,hphi]
  simp only [incrementsGlobalSpatialDerivative,incrementsGlobalScalarDerivative,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearEquiv.coe_coe,
    WithLp.ofLp_add,WithLp.ofLp_sub,WithLp.ofLp_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,w]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem actualRepairModelFirstDefect_array_mean_observed_total
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (phi : Label → Ep × M → ℝ) (tau : ℝ) (R Q : Label → Ep × M → V)
    (b : Ep) (x : D) (hx : x ∈ e.target) (i j : Fin (m+1)) :
    let w := fun k : Fin (m+1) => mfderiv 𝓘(ℝ,D) 𝓙 e.symm x
      ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm (EuclideanSpace.single k 1))
    (incrementsOppositePrimaryContribution
      (round4ParameterProbeArrayObservedCoefficient phi tau R Q b e.symm x) i j).re =
      round4ParameterProbeArrayMean (I := 𝓙) phi tau R Q b (e.symm x) (w i) (w j) := by
  intro w
  let coeff := round4ParameterProbeArrayObservedCoefficient phi tau R Q b e.symm x
  have hc (l : Label) (k : Fin (m+1)) (co : Fin N) : coeff l k co =
      (round4PrescribedNativeCoefficient (I := 𝓙) false (phi l) tau (R l) (Q l) (b,e.symm x) (w k) co : ℂ) +
      Complex.I * (round4PrescribedNativeCoefficient (I := 𝓙) true (phi l) tau (R l) (Q l) (b,e.symm x) (w k) co : ℂ) :=
    actualRepairModelFirstDefect_observed_coefficient_total e he (phi l) (R l) (Q l) tau b x
      (EuclideanSpace.single k 1) hx co
  have ht (l : Label) : ((1/4 : ℂ)*
      ((coeff l i ⬝ᵥ (fun co => conj (coeff l j co))) +
        ((fun co => conj (coeff l i co)) ⬝ᵥ coeff l j))).re = (1/2 : ℝ)*
      (inner ℝ (round4PrescribedNativeCoefficient (I := 𝓙) false (phi l) tau (R l) (Q l) (b,e.symm x) (w i))
        (round4PrescribedNativeCoefficient (I := 𝓙) false (phi l) tau (R l) (Q l) (b,e.symm x) (w j)) +
      inner ℝ (round4PrescribedNativeCoefficient (I := 𝓙) true (phi l) tau (R l) (Q l) (b,e.symm x) (w i))
        (round4PrescribedNativeCoefficient (I := 𝓙) true (phi l) tau (R l) (Q l) (b,e.symm x) (w j))) := by
    rw [show (1/4 : ℂ) = ((1/4 : ℝ) : ℂ) by norm_num]
    simp only [dotProduct,hc,Complex.mul_re,Complex.add_re,Complex.mul_im,Complex.add_im,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,Complex.re_sum,Complex.im_sum,zero_mul,mul_zero,one_mul,zero_add,add_zero,
      sub_zero,PiLp.inner_apply,Real.inner_apply]
    ring_nf
    rw [Finset.sum_add_distrib]
    ring
  change (incrementsOppositePrimaryContribution coeff i j).re = _
  unfold incrementsOppositePrimaryContribution
  rw [Complex.re_sum]
  simp_rw [ht]
  simp only [round4ParameterProbeArrayMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul,Finset.mul_sum]

theorem actualRepairModelFirstDefect_array_mean_original_total
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas)
    (phase : Label → Ep × M → ℝ) (tau : ℝ) (R Q : Label → Ep × M → V)
    (i : Fin atlas.count × Fin count) (z : X) (hz : z.2 ∈ (atlas.chart i.1).target) :
    actualOriginalNativeTargetTensor atlas param
      (round4ParameterProbeArrayMean (I := 𝓙) phase tau R Q) i z =
    actualPrimaryOppositeMeanTensor
      (fun l t x => phase l ((param i.2).symm t,(atlas.chart i.1).symm x)) tau
      (fun (_ : Label) (_ : Ep) (_ : Unit) (_ : D) => 1)
      (fun l t (_ : Unit) x => R l ((param i.2).symm t,(atlas.chart i.1).symm x))
      (fun l t (_ : Unit) x => Q l ((param i.2).symm t,(atlas.chart i.1).symm x)) z := by
  apply actual_bilinear_tensor_eq_of_basis
  intro k l
  simp only [actualOriginalNativeTargetTensor_basis,actualPrimaryOppositeMeanTensor,
    actualRealTensorAssembly_basis]
  exact (actualRepairModelFirstDefect_array_mean_observed_total (atlas.chart i.1) (hAtlas.chart_mem i.1)
    phase tau R Q ((param i.2).symm z.1) z.2 hz k l).symm

theorem actualRepairModelFirstDefect_array_rest_pullback_total
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F U : Ep × M → V) (phase : Label → Ep × M → ℝ)
    (tau : ℝ) (R Q : Label → Ep × M → V)
    (i : Fin A.count × Fin count) (z : X)
    (hz : z ∈ (B i.2).target ×ˢ (A.chart i.1).target) :
    actualOriginalNativeTargetTensor A B
      (actualRepairModelFirstDefectArrayRest F U phase tau R Q) i z =
    (actualRepairModelFirstDefectObservedRest F U phase tau R Q (A.chart i.1) ∘
      parameterRound2_meanParameterMap (m := m) (B i.2)) z := by
  rw [actualRepairModelFirstDefectArrayRest,
    actual_original_native_metric_error_pullback_total A B hA F U _ 1 i z hz]
  have hm := actualRepairModelFirstDefect_array_mean_original_total A B hA phase tau R Q i z hz.2
  simp only [actualOriginalNativeMetricError,actualFiniteMetricError,one_pow,one_smul]
  rw [hm]
  simp only [actualRepairModelFirstDefectObservedRest,Function.comp_apply,
    parameterRound2_meanParameterMap,actualFiniteMetricError,one_pow,one_smul]
  apply actual_bilinear_tensor_eq_of_basis
  intro k l
  simp only [sub_apply,zero_apply,sub_zero]
  rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_observed_coefficient_total
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_array_rest_pullback_total
