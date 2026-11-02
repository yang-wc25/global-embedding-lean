import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Tactic.Module

/-!
# Actual scaling algebra for normalized pairing inverses

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines477–489.
The complementary idempotent mask records exactly the columns divided by epsilon.
-/

noncomputable section
open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual data scale: unchanged coordinates have factor1 and masked ones factor epsilon. -/
def freeColumnScale (J : V →L[ℝ] V) (ε : ℝ) : V →L[ℝ] V :=
  (ContinuousLinearMap.id ℝ V - J) + ε • J

/-- The literal regularized inverse scale, defined at zero without division. -/
def freeInverseScale (J : V →L[ℝ] V) (ε : ℝ) : V →L[ℝ] V :=
  ε • (ContinuousLinearMap.id ℝ V - J) + J

/-- Multiplying the actual scales gives epsilon times the identity, including at zero. -/
theorem freeColumnScale_comp_inverseScale (J : V →L[ℝ] V)
    (hJ : J.comp J = J) (ε : ℝ) :
    (freeColumnScale J ε).comp (freeInverseScale J ε) = ε • ContinuousLinearMap.id ℝ V := by
  have hJJ (v : V) : J (J v) = J v := congrArg (fun A : V →L[ℝ] V ↦ A v) hJ
  ext v
  simp only [freeColumnScale, freeInverseScale, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_add, map_sub, map_smul,
    hJJ]
  module

/-- The scales commute, so the reverse product is the same scalar identity. -/
theorem freeInverseScale_comp_columnScale (J : V →L[ℝ] V)
    (hJ : J.comp J = J) (ε : ℝ) :
    (freeInverseScale J ε).comp (freeColumnScale J ε) = ε • ContinuousLinearMap.id ℝ V := by
  have hJJ (v : V) : J (J v) = J v := congrArg (fun A : V →L[ℝ] V ↦ A v) hJ
  ext v
  simp only [freeColumnScale, freeInverseScale, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_add, map_sub, map_smul,
    hJJ]
  module

/-- The normalized inverse is the literal projected Gram reconstruction with the regularized
inverse scale. This definition imposes no condition on its value at epsilon zero. -/
def freeNormalizedPairingInverse (prj : E →L[ℝ] E) (R : V →L[ℝ] E)
    (J : V →L[ℝ] V) (ε : ℝ) : V →L[ℝ] E :=
  prj.comp (R.comp (freeInverseScale J ε))

/-- The actual inverse away from epsilon zero, defined as a total function for convenience. -/
def freePairingInverse (prj : E →L[ℝ] E) (R : V →L[ℝ] E)
    (J : V →L[ℝ] V) (ε : ℝ) : V →L[ℝ] E :=
  ε⁻¹ • freeNormalizedPairingInverse prj R J ε

/-- Actual normalized pairing data reconstruct the complete scaled identity on every datum. -/
theorem free_normalized_pairing_identity (J : V →L[ℝ] V)
    (hJ : J.comp J = J) (ε : ℝ) (T : E →L[ℝ] V) (prj : E →L[ℝ] E)
    (B : E →L[ℝ] V) (R : V →L[ℝ] E)
    (hTB : T.comp prj = (freeColumnScale J ε).comp B)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ V) :
    T.comp (freeNormalizedPairingInverse prj R J ε) = ε • ContinuousLinearMap.id ℝ V := by
  calc
    _ = ((freeColumnScale J ε).comp B).comp (R.comp (freeInverseScale J ε)) := by
      rw [freeNormalizedPairingInverse, ← ContinuousLinearMap.comp_assoc, hTB]
    _ = (freeColumnScale J ε).comp ((B.comp R).comp (freeInverseScale J ε)) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = (freeColumnScale J ε).comp (freeInverseScale J ε) := by
      rw [hBR, ContinuousLinearMap.id_comp]
    _ = _ := freeColumnScale_comp_inverseScale J hJ ε

/-- At nonzero epsilon, the literal reconstruction is a right inverse on the full data space. -/
theorem free_pairing_right_inverse (J : V →L[ℝ] V) (hJ : J.comp J = J)
    (ε : ℝ) (hε : ε ≠ 0) (T : E →L[ℝ] V) (prj : E →L[ℝ] E)
    (B : E →L[ℝ] V) (R : V →L[ℝ] E)
    (hTB : T.comp prj = (freeColumnScale J ε).comp B)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ V) :
    T.comp (freePairingInverse prj R J ε) = ContinuousLinearMap.id ℝ V := by
  rw [freePairingInverse, ContinuousLinearMap.comp_smul,
    free_normalized_pairing_identity J hJ ε T prj B R hTB hBR, smul_smul,
    inv_mul_cancel₀ hε, one_smul]

/-- Epsilon times the actual inverse equals the same normalized extension only away from zero. -/
theorem free_pairing_inverse_scaled (prj : E →L[ℝ] E) (R : V →L[ℝ] E)
    (J : V →L[ℝ] V) (ε : ℝ) (hε : ε ≠ 0) :
    ε • freePairingInverse prj R J ε = freeNormalizedPairingInverse prj R J ε := by
  rw [freePairingInverse, smul_smul, mul_inv_cancel₀ hε, one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The genuine column scale is a smooth polynomial family through epsilon zero. -/
theorem freeColumnScale_contDiff (J : V →L[ℝ] V) :
    ContDiff ℝ ∞ (freeColumnScale J) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The genuine inverse scale is polynomial and smooth through epsilon zero. -/
theorem freeInverseScale_contDiff (J : V →L[ℝ] V) :
    ContDiff ℝ ∞ (freeInverseScale J) :=
  (contDiff_id.smul contDiff_const).add contDiff_const

/-- Native smooth input reconstruction gives a genuinely smooth normalized inverse through zero. -/
theorem freeNormalizedPairingInverse_contMDiff
    {P H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ P H}
    [TopologicalSpace M] [ChartedSpace H M]
    (J : V →L[ℝ] V) (prj : M → E →L[ℝ] E) (R : M → V →L[ℝ] E) (ε : M → ℝ)
    (hprj : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ prj)
    (hR : ContMDiff I 𝓘(ℝ, V →L[ℝ] E) ∞ R)
    (hε : ContMDiff I 𝓘(ℝ, ℝ) ∞ ε) :
    ContMDiff I 𝓘(ℝ, V →L[ℝ] E) ∞
      (fun x ↦ freeNormalizedPairingInverse (prj x) (R x) J (ε x)) :=
  hprj.clm_comp (hR.clm_comp ((freeInverseScale_contDiff J).contMDiff.comp hε))

#print axioms free_normalized_pairing_identity
#print axioms free_pairing_right_inverse
#print axioms free_pairing_inverse_scaled
#print axioms freeNormalizedPairingInverse_contMDiff

end GlobalEmbedding.Paper
