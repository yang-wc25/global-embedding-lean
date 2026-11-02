import Probes.ActualScaledProbe
import GlobalEmbedding.Offline.ActualPairedValueRemainder

/-!
# Actual finite sine/cosine probe family and its parameter/spatial responses

Source: (8.3) and the leading terms in (8.1). This uses the EXISTING finite
paired-value map, with the source's fixed negative weight and cutoff/normal
field. Thus the native parameter columns, both spatial Hessians and the
previous coincidence-rank consumer refer to one literal finite displacement.
This is the leading homogeneous wave; background and solver corrections and
exact-metric repair are not included in this definition.
-/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p r : ℕ}

/-- The original finite paired real displacement. Every wave keeps its
original distinct parameter labels and its fixed nonzero weight. -/
def actualFiniteProbeDisplacement (label : (Fin r × Bool) ↪ Fin p)
    (δ τ : ℝ) (weight : Fin r → ℝ) (phase : Fin r → E → ℝ)
    (amplitude : Fin r → E → F) (u : Fin p → ℝ) (x : E) : F :=
  pairedValuePrincipalMap label (fun i ↦ weight i * phase i x / τ) (δ * τ)
    (fun i ↦ (-(weight i ^ 2)⁻¹) • amplitude i x) u

/-- The map is exactly the finite sum of the cosine and sine real waves,
with the amplitude prescribed by (8.3), not an arbitrary derivative family. -/
theorem actualFiniteProbeDisplacement_eq_sum
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) :
    actualFiniteProbeDisplacement label δ τ weight phase amplitude u x =
      ∑ i, ((u (label (i, false))) •
          actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i) x +
        (u (label (i, true))) •
          actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i) x) := by
  classical
  simp only [actualFiniteProbeDisplacement, pairedValuePrincipalMap,
    sum_apply, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [actualProbeCosColumn, actualProbeSinColumn, probeFastPhase_eq,
    div_eq_mul_inv]
  module

/-- The native parameter derivative of the actual finite family. -/
theorem hasFDerivAt_actualFiniteProbeDisplacement
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) :
    HasFDerivAt (fun w ↦ actualFiniteProbeDisplacement label δ τ weight phase amplitude w x)
      (pairedValuePrincipalMap label (fun i ↦ weight i * phase i x / τ) (δ * τ)
        (fun i ↦ (-(weight i ^ 2)⁻¹) • amplitude i x)) u :=
  (pairedValuePrincipalMap label (fun i ↦ weight i * phase i x / τ) (δ * τ)
    (fun i ↦ (-(weight i ^ 2)⁻¹) • amplitude i x)).hasFDerivAt

/-- The true cosine parameter column, including the sign and the `lam⁻²` weight. -/
theorem actualFiniteProbeDisplacement_cos_response
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) :
    fderiv ℝ (fun w ↦ actualFiniteProbeDisplacement label δ τ weight phase amplitude w x) u
      (Pi.single (label (i, false)) 1) =
      actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i) x := by
  rw [(hasFDerivAt_actualFiniteProbeDisplacement label δ τ weight phase amplitude u x).fderiv,
    pairedValuePrincipalMap_cos_column]
  simp only [actualProbeCosColumn, probeFastPhase_eq, div_eq_mul_inv]
  module

/-- The true sine parameter column of the SAME finite family. -/
theorem actualFiniteProbeDisplacement_sin_response
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) :
    fderiv ℝ (fun w ↦ actualFiniteProbeDisplacement label δ τ weight phase amplitude w x) u
      (Pi.single (label (i, true)) 1) =
      actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i) x := by
  rw [(hasFDerivAt_actualFiniteProbeDisplacement label δ τ weight phase amplitude u x).fderiv,
    pairedValuePrincipalMap_sin_column]
  simp only [actualProbeSinColumn, probeFastPhase_eq, div_eq_mul_inv]
  module

/-- The actual cosine parameter response, differentiated TWICE spatially,
with the original principal coefficient and the actual retained remainder. -/
theorem actualFiniteProbeDisplacement_cos_response_hessian
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0)
    (hphase : ContDiff ℝ 2 (phase i)) (hamplitude : ContDiff ℝ 2 (amplitude i)) :
    fderiv ℝ (fderiv ℝ (fun z ↦
      fderiv ℝ (fun w ↦ actualFiniteProbeDisplacement label δ τ weight phase amplitude w z) u
        (Pi.single (label (i, false)) 1))) x =
      ((δ / τ) * Real.cos (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      actualProbeCosRemainder δ τ (weight i) (phase i) (amplitude i) x := by
  have heq : (fun z ↦
      fderiv ℝ (fun w ↦ actualFiniteProbeDisplacement label δ τ weight phase amplitude w z) u
        (Pi.single (label (i, false)) 1)) =
      actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i) := by
    funext z
    exact actualFiniteProbeDisplacement_cos_response label δ τ weight phase amplitude u z i
  rw [heq]
  exact actualProbeCosColumn_hessian hphase hamplitude δ τ (weight i) hτ hw x

/-- The matching actual sine response and Hessian, with the same family,
parameter labels, weight, phase and slow remainder bound. -/
theorem actualFiniteProbeDisplacement_sin_response_hessian
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0)
    (hphase : ContDiff ℝ 2 (phase i)) (hamplitude : ContDiff ℝ 2 (amplitude i)) :
    fderiv ℝ (fderiv ℝ (fun z ↦
      fderiv ℝ (fun w ↦ actualFiniteProbeDisplacement label δ τ weight phase amplitude w z) u
        (Pi.single (label (i, true)) 1))) x =
      ((δ / τ) * Real.sin (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      actualProbeSinRemainder δ τ (weight i) (phase i) (amplitude i) x := by
  have heq : (fun z ↦
      fderiv ℝ (fun w ↦ actualFiniteProbeDisplacement label δ τ weight phase amplitude w z) u
        (Pi.single (label (i, true)) 1)) =
      actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i) := by
    funext z
    exact actualFiniteProbeDisplacement_sin_response label δ τ weight phase amplitude u z i
  rw [heq]
  exact actualProbeSinColumn_hessian hphase hamplitude δ τ (weight i) hτ hw x

#print axioms actualFiniteProbeDisplacement_eq_sum
#print axioms hasFDerivAt_actualFiniteProbeDisplacement
#print axioms actualFiniteProbeDisplacement_cos_response_hessian
#print axioms actualFiniteProbeDisplacement_sin_response_hessian

end GlobalEmbedding.Offline
