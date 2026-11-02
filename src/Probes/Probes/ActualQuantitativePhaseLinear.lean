import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual triangular differential of parameter-preserving phase coordinates

The map replaces one spatial coordinate by the original phase and leaves the
parameter and the transverse coordinates unchanged. Its inverse is constructed
from the original phase differential, with an explicit native operator bound.
No adapted chart or inverse estimate is an input.
-/

noncomputable section
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep Et : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et]

def actualPhaseTransverse : (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)) :=
  (ContinuousLinearMap.fst ℝ Ep (ℝ × Et)).prod
    ((0 : (Ep × (ℝ × Et)) →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ Et).comp (ContinuousLinearMap.snd ℝ Ep (ℝ × Et))))

def actualPhaseTriangular (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ) :
    (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)) :=
  (ContinuousLinearMap.fst ℝ Ep (ℝ × Et)).prod
    (d.prod ((ContinuousLinearMap.snd ℝ ℝ Et).comp
      (ContinuousLinearMap.snd ℝ Ep (ℝ × Et))))

def actualPhaseTriangularInverse (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ) :
    (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)) :=
  (ContinuousLinearMap.fst ℝ Ep (ℝ × Et)).prod
    (((d (0,(1,0)))⁻¹ •
      ((ContinuousLinearMap.fst ℝ ℝ Et).comp (ContinuousLinearMap.snd ℝ Ep (ℝ × Et)) -
        d.comp actualPhaseTransverse)).prod
      ((ContinuousLinearMap.snd ℝ ℝ Et).comp (ContinuousLinearMap.snd ℝ Ep (ℝ × Et))))

theorem actual_phase_differential_decomposition
    (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ) (z : Ep × (ℝ × Et)) :
    d z = d (z.1,(0,z.2.2)) + z.2.1 * d (0,(1,0)) := by
  have hz : z = (z.1,(0,z.2.2)) + z.2.1 • (0,(1,0)) := by
    ext <;> simp
  calc
    d z = d ((z.1,(0,z.2.2)) + z.2.1 • (0,(1,0))) := congrArg d hz
    _ = _ := by rw [map_add,map_smul]; rfl

def actualPhaseTriangularEquiv (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ)
    (hd : d (0,(1,0)) ≠ 0) : (Ep × (ℝ × Et)) ≃L[ℝ] (Ep × (ℝ × Et)) :=
  ContinuousLinearEquiv.equivOfInverse (actualPhaseTriangular d) (actualPhaseTriangularInverse d)
    (by
      intro z
      refine Prod.ext ?_ ?_
      · rfl
      refine Prod.ext ?_ ?_
      rotate_left
      · rfl
      change (d (0,(1,0)))⁻¹ * (d z - d (z.1,(0,z.2.2))) = z.2.1
      rw [actual_phase_differential_decomposition d z]
      field_simp
      ring)
    (by
      intro z
      refine Prod.ext ?_ ?_
      · rfl
      refine Prod.ext ?_ ?_
      rotate_left
      · rfl
      change d (z.1,((d (0,(1,0)))⁻¹ * (z.2.1-d (z.1,(0,z.2.2))),z.2.2)) = z.2.1
      rw [actual_phase_differential_decomposition]
      field_simp
      ring)

@[simp] theorem actualPhaseTriangularEquiv_apply
    (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ) (hd : d (0,(1,0)) ≠ 0) (z : Ep × (ℝ × Et)) :
    actualPhaseTriangularEquiv d hd z = (z.1,(d z,z.2.2)) := rfl

@[simp] theorem actualPhaseTriangularEquiv_symm_apply
    (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ) (hd : d (0,(1,0)) ≠ 0) (z : Ep × (ℝ × Et)) :
    (actualPhaseTriangularEquiv d hd).symm z =
      (z.1,((d (0,(1,0)))⁻¹ * (z.2.1-d (z.1,(0,z.2.2))),z.2.2)) := rfl

theorem actual_phase_triangular_inverse_bound
    (d : (Ep × (ℝ × Et)) →L[ℝ] ℝ) (hd : d (0,(1,0)) ≠ 0) :
    ‖((actualPhaseTriangularEquiv d hd).symm :
      (Ep × (ℝ × Et)) →L[ℝ] (Ep × (ℝ × Et)))‖ ≤
        1 + (1+‖d‖)/|d (0,(1,0))| := by
  have ha : 0 < |d (0,(1,0))| := abs_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hp : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hs : |z.2.1| ≤ ‖z‖ := (norm_fst_le z.2).trans (norm_snd_le z)
  have ht : ‖z.2.2‖ ≤ ‖z‖ := (norm_snd_le z.2).trans (norm_snd_le z)
  have hz0 : ‖(z.1,((0:ℝ),z.2.2))‖ ≤ ‖z‖ := by
    rw [Prod.norm_def,Prod.norm_def,norm_zero, max_eq_right (norm_nonneg _)]
    exact max_le hp ht
  have hdz : |d (z.1,((0:ℝ),z.2.2))| ≤ ‖d‖ * ‖z‖ :=
    (d.le_opNorm _).trans (mul_le_mul_of_nonneg_left hz0 (norm_nonneg _))
  have hcoord : |(d (0,(1,0)))⁻¹ * (z.2.1-d (z.1,(0,z.2.2)))| ≤
      ((1+‖d‖)/|d (0,(1,0))|) * ‖z‖ := by
    rw [abs_mul,abs_inv]
    calc
      _ ≤ |d (0,(1,0))|⁻¹ * (|z.2.1|+|d (z.1,(0,z.2.2))|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (inv_nonneg.mpr ha.le)
      _ ≤ |d (0,(1,0))|⁻¹ * (‖z‖ + ‖d‖*‖z‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hs hdz) (inv_nonneg.mpr ha.le)
      _ = _ := by ring
  change ‖(z.1,((d (0,(1,0)))⁻¹*(z.2.1-d (z.1,(0,z.2.2))),z.2.2))‖ ≤ _
  rw [Prod.norm_def,Prod.norm_def,Real.norm_eq_abs]
  have hbase : ‖z‖ ≤ (1+(1+‖d‖)/|d (0,(1,0))|)*‖z‖ := by
    nlinarith [div_nonneg (show 0 ≤ 1+‖d‖ by positivity) ha.le,norm_nonneg z]
  have hcoord' : ((1+‖d‖)/|d (0,(1,0))|)*‖z‖ ≤
      (1+(1+‖d‖)/|d (0,(1,0))|)*‖z‖ := by nlinarith [norm_nonneg z]
  exact max_le (hp.trans hbase) (max_le (hcoord.trans hcoord') (ht.trans hbase))

theorem actual_phase_triangular_difference_bound
    (d e : (Ep × (ℝ × Et)) →L[ℝ] ℝ) :
    ‖actualPhaseTriangular d - actualPhaseTriangular e‖ ≤ ‖d-e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  have h := (d-e).le_opNorm z
  change ‖(z.1,(d z,z.2.2))-(z.1,(e z,z.2.2))‖ ≤ _
  simpa [Prod.norm_def] using h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_phase_triangular_inverse_bound
