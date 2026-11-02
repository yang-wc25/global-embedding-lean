import Probes.Round4PrescribedNativeMeanParity
import GlobalEmbedding.Paper.IncrementsFullNormalizedPrimaryError

/-!
# Native coefficients of the actual globally reconstructed field in a real chart

The target tangent cast and the source-only manifold derivative are retained.
The observed complex coefficient is the original derivative coefficient of the
complete real and imaginary amplitudes. No leading-wave replacement or native
coefficient identity is postulated.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set
open scoped ContDiff BigOperators ComplexConjugate
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual chart observation of the source differential. -/
theorem round4_native_observation_derivative
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Ep × M → Y) (b : Ep) (obs : D → M) (x v : D)
    (hf : ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,Y) ∞ f (b,obs x))
    (hobs : ContMDiffAt 𝓘(ℝ,D) I ∞ obs x) :
    fderiv ℝ (fun y => f (b,obs y)) x v =
      (tangentSpaceCastModel 𝓘(ℝ,Y) (f (b,obs x)))
        (mfderiv I 𝓘(ℝ,Y) (fun y => f (b,y)) (obs x)
          (mfderiv 𝓘(ℝ,D) I obs x ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm v))) := by
  have hslice := (hf.comp (obs x)
    ((contMDiffAt_const (c:=b)).prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp x hslice (hobs.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  exact congrArg (fun L => L v) hchain

/-- The same complete complex derivative coefficient, expressed through its
actual native real and imaginary maps after a genuine smooth observation. -/
theorem round4_native_observed_coefficient
    (phi : Ep × M → ℝ) (R Q : Ep × M → V) (tau : ℝ)
    (b : Ep) (obs : D → M) (x v : D) (co : Fin N)
    (hp : ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ phi (b,obs x))
    (hR : ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ R (b,obs x))
    (hQ : ContMDiffAt ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,V) ∞ Q (b,obs x))
    (hobs : ContMDiffAt 𝓘(ℝ,D) I ∞ obs x) :
    let w := mfderiv 𝓘(ℝ,D) I obs x ((tangentSpaceCastModel 𝓘(ℝ,D) x).symm v)
    incrementsPrimaryDerivativeCoefficient (fun y => phi (b,obs y)) tau
      (fun (_ : Unit) _ => 1) (fun _ y => R (b,obs y)) (fun _ y => Q (b,obs y)) x v co =
      (round4PrescribedNativeCoefficient (I:=I) false phi tau R Q (b,obs x) w co : ℂ) +
      Complex.I * (round4PrescribedNativeCoefficient (I:=I) true phi tau R Q (b,obs x) w co : ℂ) := by
  intro w
  have hr := round4_native_observation_derivative R b obs x v hR hobs
  have hq := round4_native_observation_derivative Q b obs x v hQ hobs
  have hphi := round4_native_observation_derivative phi b obs x v hp hobs
  simp only [incrementsPrimaryDerivativeCoefficient,Finset.univ_unique,Finset.sum_singleton,
    fderiv_const_apply,ContinuousLinearMap.zero_apply,Complex.ofReal_zero,mul_zero,zero_mul,
    one_mul,Complex.ofReal_one,zero_add]
  change _ =
    ((incrementsGlobalSpatialDerivative (I:=I) R (b,obs x) w -
      incrementsGlobalScalarDerivative (I:=I) phi (b,obs x) w • (tau⁻¹ • Q (b,obs x))) co : ℂ) +
    Complex.I * ((incrementsGlobalSpatialDerivative (I:=I) Q (b,obs x) w +
      incrementsGlobalScalarDerivative (I:=I) phi (b,obs x) w • (tau⁻¹ • R (b,obs x))) co : ℂ)
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

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_native_observation_derivative
#print axioms GlobalEmbedding.Continuation.round4_native_observed_coefficient
