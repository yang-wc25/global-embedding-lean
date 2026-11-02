import Probes.ActualIncrementPrimaryWaveBinding
import Probes.ActualIncrementPrimaryGlobalSupport

/-! Exact coefficient bindings for the SAME original primary wave. Real
homogeneity uses totalized native differentiation and needs no artificial
coefficient assumption. The observation/native identity is an actual manifold
chain rule through the observation inverse, with the genuine vector. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

theorem actual_primary_derivative_coefficient_smul
    {a N : ℕ} {Β : Type*} [Fintype Β]
    (phi : EuclideanSpace ℝ (Fin a) → ℝ) (tau delta : ℝ)
    (chi : Β → EuclideanSpace ℝ (Fin a) → ℝ)
    (P Q : Β → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin a)) :
    incrementsPrimaryDerivativeCoefficient phi tau chi
      (fun β y => delta • P β y) (fun β y => delta • Q β y) x v =
      delta • incrementsPrimaryDerivativeCoefficient phi tau chi P Q x v := by
  have hP (β : Β) : fderiv ℝ (fun y => delta • P β y) x = delta • fderiv ℝ (P β) x :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := P β) delta) x
  have hQ (β : Β) : fderiv ℝ (fun y => delta • Q β y) x = delta • fderiv ℝ (Q β) x :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := Q β) delta) x
  ext c
  simp only [incrementsPrimaryDerivativeCoefficient, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [hP β,hQ β]
  simp only [ContinuousLinearMap.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.real_smul]
  ring

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

variable (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

/-- These are exactly the amplitudes in the literal global-wave binding. -/
theorem actual_original_primary_physical_coefficient_binding
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau delta : ℝ) (e : OpenPartialHomeomorph M D) (z : X) (ν : Λ) :
    incrementsSecondaryPhysicalCoefficient
      (fun mu b x => g.phase mu (b,e.symm x)) tau (fun _ _ _ _ => 1)
      (fun mu b β x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true mu β (b,e.symm x))
      (fun mu b β x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false mu β (b,e.symm x))
      (fun r _ => EuclideanSpace.single r 1) z ν =
        delta • incrementsGlobalObservedCoefficient F hF g input length tau e z.1 z.2 ν := by
  funext r
  exact actual_primary_derivative_coefficient_smul _ tau delta _ _ _ _ _

private theorem observed_native_derivative {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : M → Y) (e : OpenPartialHomeomorph M D) (y v : D)
    (he : MDifferentiableAt 𝓘(ℝ,D) I e.symm y)
    (hf : MDifferentiableAt I 𝓘(ℝ,Y) f (e.symm y)) :
    fderiv ℝ (f ∘ e.symm) y v =
      (tangentSpaceCastModel 𝓘(ℝ,Y) (f (e.symm y)))
        (mfderiv I 𝓘(ℝ,Y) f (e.symm y)
          (mfderiv 𝓘(ℝ,D) I e.symm y
            ((tangentSpaceCastModel 𝓘(ℝ,D) y).symm v))) := by
  have h := mfderiv_comp y hf he
  rw [mfderiv_eq_fderiv] at h
  exact congrArg (fun L => L v) h

private theorem observed_native_total_derivative {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : M → Y) (e : OpenPartialHomeomorph M D) (y v : D)
    (he : e.MDifferentiable I 𝓘(ℝ,D)) (hy : y ∈ e.target) :
    fderiv ℝ (f ∘ e.symm) y v =
      (tangentSpaceCastModel 𝓘(ℝ,Y) (f (e.symm y)))
        (mfderiv I 𝓘(ℝ,Y) f (e.symm y)
          (mfderiv 𝓘(ℝ,D) I e.symm y
            ((tangentSpaceCastModel 𝓘(ℝ,D) y).symm v))) := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ,Y) f (e.symm y)
  · exact observed_native_derivative f e y v (he.mdifferentiableAt_symm hy) hf
  · have hn : ¬ DifferentiableAt ℝ (f ∘ e.symm) y := by
      intro h
      have ho : MDifferentiableAt 𝓘(ℝ,D) 𝓘(ℝ,Y) (f ∘ e.symm) (e (e.symm y)) := by
        rw [e.right_inv hy]
        exact h.mdifferentiableAt
      have hcomp := ho.comp (e.symm y) (he.mdifferentiableAt (e.map_target hy))
      have heq : f =ᶠ[𝓝 (e.symm y)] ((f ∘ e.symm) ∘ e) := by
        filter_upwards [e.open_source.mem_nhds (e.map_target hy)] with x hx
        simp only [Function.comp_apply,e.left_inv hx]
      exact hf (hcomp.congr_of_eventuallyEq heq)
    rw [fderiv_zero_of_not_differentiableAt hn, mfderiv_zero_of_not_mdifferentiableAt hf]
    rfl

/-- The observed complex coefficient is the real/imaginary pair of the SAME
native coefficient maps, evaluated on the true inverse-chart tangent vector. -/
theorem actual_original_observed_coefficient_native
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (e : OpenPartialHomeomorph M D) (t : Ep) (y : D) (ν : Λ)
    (he : e.MDifferentiable I 𝓘(ℝ,D)) (hy : y ∈ e.target)
    (hExt : ∀ (ch : Bool) β, MDifferentiableAt I 𝓘(ℝ,V)
      (fun x => incrementsGlobalPrimaryExtension F hF g input length tau ch ν β (t,x)) (e.symm y))
    (r : Fin (m+1)) (co : Fin N) :
    incrementsGlobalObservedCoefficient F hF g input length tau e t y ν r co =
      (incrementsGlobalPrimaryCoefficient F hF g input length tau true ν (t,e.symm y)
        (incrementsGlobalObservationVector (I := I) e y r) co : ℂ) + Complex.I *
      (incrementsGlobalPrimaryCoefficient F hF g input length tau false ν (t,e.symm y)
        (incrementsGlobalObservationVector (I := I) e y r) co : ℂ) := by
  have hInv := he.mdifferentiableAt_symm hy
  let R := fun β x => incrementsGlobalPrimaryExtension F hF g input length tau true ν β (t,e.symm x)
  let Q := fun β x => incrementsGlobalPrimaryExtension F hF g input length tau false ν β (t,e.symm x)
  let AR := fun x => incrementsGlobalPrimaryAmplitude F hF g input length tau true ν (t,e.symm x)
  let AI := fun x => incrementsGlobalPrimaryAmplitude F hF g input length tau false ν (t,e.symm x)
  let C := incrementsFreeComplexCoordinate co
  have hAmp (ch : Bool) : MDifferentiableAt I 𝓘(ℝ,V)
      (fun x => incrementsGlobalPrimaryAmplitude F hF g input length tau ch ν (t,x)) (e.symm y) := by
    have hs : (fun x => incrementsGlobalPrimaryAmplitude F hF g input length tau ch ν (t,x)) =
        ∑ β, (fun x => incrementsGlobalPrimaryExtension F hF g input length tau ch ν β (t,x)) := by
      funext x
      simp only [incrementsGlobalPrimaryAmplitude,Finset.sum_apply]
    rw [hs]
    exact MDifferentiableAt.sum (fun β _ => hExt ch β)
  have hAR : DifferentiableAt ℝ AR y := ((hAmp true).comp y hInv).differentiableAt
  have hAI : DifferentiableAt ℝ AI y := ((hAmp false).comp y hInv).differentiableAt
  have hR (β : Β) : DifferentiableAt ℝ (R β) y := ((hExt true β).comp y hInv).differentiableAt
  have hQ (β : Β) : DifferentiableAt ℝ (Q β) y := ((hExt false β).comp y hInv).differentiableAt
  have hsum : incrementsPrimaryCorrectionSum R Q co = fun x => C (AR x)+Complex.I • C (AI x) := by
    funext x
    simp only [incrementsPrimaryCorrectionSum, AR, AI, incrementsGlobalPrimaryAmplitude,
      map_sum, Finset.smul_sum, Finset.sum_add_distrib, R, Q, C]
  have hjet := (C.hasFDerivAt.comp y hAR.hasFDerivAt).add
    ((C.hasFDerivAt.comp y hAI.hasFDerivAt).const_smul Complex.I)
  have hh := increments_primary_correction_coefficient_eq
    (fun x => g.phase ν (t,e.symm x)) tau R Q y (EuclideanSpace.single r 1) co hR hQ
  change HasFDerivAt (fun x => C (AR x)+Complex.I • C (AI x))
    (C.comp (fderiv ℝ AR y)+Complex.I • C.comp (fderiv ℝ AI y)) y at hjet
  rw [hsum,hjet.fderiv] at hh
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] at hh
  have hAmpJet (ch : Bool) :
      fderiv ℝ (fun x => incrementsGlobalPrimaryAmplitude F hF g input length tau ch ν (t,e.symm x))
        y (EuclideanSpace.single r 1) =
      incrementsGlobalSpatialDerivative (I := I)
        (incrementsGlobalPrimaryAmplitude F hF g input length tau ch ν)
        (t,e.symm y) (incrementsGlobalObservationVector (I := I) e y r) :=
    observed_native_derivative _ e y _ hInv (hAmp ch)
  dsimp only [AR,AI] at hh
  rw [hAmpJet true,hAmpJet false] at hh
  have hp : fderiv ℝ (fun x => g.phase ν (t,e.symm x)) y (EuclideanSpace.single r 1) =
      incrementsGlobalScalarDerivative (I := I) (g.phase ν) (t,e.symm y)
        (incrementsGlobalObservationVector (I := I) e y r) :=
    observed_native_total_derivative (fun x => g.phase ν (t,x)) e y (EuclideanSpace.single r 1) he hy
  rw [hp] at hh
  change incrementsGlobalObservedCoefficient F hF g input length tau e t y ν r co = _ at hh
  rw [hh]
  have hC (u : V) : C u = (u co : ℂ) := rfl
  simp only [hC,smul_eq_mul,incrementsGlobalPrimaryCoefficient,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,ite_false,ite_true,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smulRight_apply,
    WithLp.ofLp_add,WithLp.ofLp_sub,WithLp.ofLp_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_derivative_coefficient_smul
#print axioms GlobalEmbedding.Continuation.actual_original_primary_physical_coefficient_binding
#print axioms GlobalEmbedding.Continuation.actual_original_observed_coefficient_native
