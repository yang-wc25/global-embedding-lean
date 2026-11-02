import NormalPolar.ActualProbeSecondaryScales
import NormalPolar.ParameterDisplacementNorms

/-!
# Fixed constants and a common scale for the original probe components

The sharp background accepts the ratio epsilon = tau/ell, while the selected
initial state and target recentering accept their own fixed upper bounds on t.
This public interface selects one positive threshold before t. It never
changes the initialized parameter ball, the source atlas, or any mapping family.

The secondary's native response modulus remains the original vanishing
C |t|^(38/5). Only its coefficient in the C1/C2 parameter norm is paid by a
fixed constant on 0 < t <= 1; a t-dependent coefficient is not silently used
as the shared constant of ActualProbeFirstModelBounds.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar

/-- A fixed threshold meeting the selected initial-state, target-center and
sharp-background conditions. The last condition is on tau/ell = t^(1/10),
not on tau alone. -/
def probesCommonThreshold (initialCap centerCap sharpCap : ℝ) : ℝ :=
  min initialCap (min centerCap (min (1/2) ((min sharpCap 1 / 2)^10)))

theorem probesCommonThreshold_pos {initialCap centerCap sharpCap : ℝ}
    (hi : 0 < initialCap) (hc : 0 < centerCap) (hs : 0 < sharpCap) :
    0 < probesCommonThreshold initialCap centerCap sharpCap := by
  unfold probesCommonThreshold
  exact lt_min hi (lt_min hc (lt_min (by norm_num)
    (pow_pos (div_pos (lt_min hs (by norm_num)) (by norm_num)) 10)))

theorem probesCommonThreshold_conditions {initialCap centerCap sharpCap : ℝ}
    (hs : 0 < sharpCap) (t : ℝ) (ht : 0 < t)
    (htt : t < probesCommonThreshold initialCap centerCap sharpCap) :
    t ≤ initialCap ∧ t ≤ centerCap ∧ t ≤ 1/2 ∧
      t^((6:ℝ)/5) / t^((11:ℝ)/10) < sharpCap := by
  have hbounds := (lt_min_iff.mp htt)
  have hrest := lt_min_iff.mp hbounds.2
  have hlast := lt_min_iff.mp hrest.2
  refine ⟨hbounds.1.le, hrest.1.le, hlast.1.le, ?_⟩
  have hsmall : 0 < min sharpCap 1 / 2 :=
    div_pos (lt_min hs (by norm_num)) (by norm_num)
  have hpower : ((min sharpCap 1 / 2)^10)^((1:ℝ)/10) = min sharpCap 1 / 2 := by
    rw [← Real.rpow_natCast (min sharpCap 1 / 2) 10,
      ← Real.rpow_mul hsmall.le]
    norm_num
  have hroot := Real.rpow_le_rpow ht.le hlast.2.le (by norm_num : (0:ℝ) ≤ 1/10)
  rw [hpower] at hroot
  have hratio : t^((6:ℝ)/5) / t^((11:ℝ)/10) = t^((1:ℝ)/10) := by
    rw [← Real.rpow_sub ht]
    congr 1
    norm_num
  rw [hratio]
  exact hroot.trans_lt ((by linarith : min sharpCap 1 / 2 < min sharpCap 1).trans_le
    (min_le_left _ _))

/-- The native secondary modulus is bounded by its fixed cost on the
original small-scale interval; it is still retained as a vanishing modulus
in the value and Hessian response estimates. -/
theorem probes_secondary_modulus_le_cost {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    actualProbeSecondaryModulus C t ≤ C := by
  unfold actualProbeSecondaryModulus
  rw [abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_one ht ht1 (by norm_num : (0:ℝ) ≤ 38/5)) hC).trans_eq (mul_one C)

/-- One fixed coefficient pays both original atlas parameter norms. -/
def probesSecondaryNormConstant (n N : ℕ) (C : ℝ) : ℝ :=
  (probeAtlasFromNativeConstant n N 1 + probeAtlasFromNativeConstant n N 2) * C

theorem probesSecondaryNormConstant_nonneg (n N : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ probesSecondaryNormConstant n N C := by
  exact mul_nonneg (add_nonneg (probeAtlasFromNativeConstant_nonneg n N 1)
    (probeAtlasFromNativeConstant_nonneg n N 2)) hC

theorem probes_secondary_norm_coefficients (n N : ℕ) {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    probeAtlasFromNativeConstant n N 1 * actualProbeSecondaryModulus C t ≤
      probesSecondaryNormConstant n N C ∧
    probeAtlasFromNativeConstant n N 2 * actualProbeSecondaryModulus C t ≤
      probesSecondaryNormConstant n N C := by
  have hmod := probes_secondary_modulus_le_cost hC ht ht1
  have h1 := probeAtlasFromNativeConstant_nonneg n N 1
  have h2 := probeAtlasFromNativeConstant_nonneg n N 2
  constructor
  · exact (mul_le_mul_of_nonneg_left hmod h1).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h2) hC)
  · exact (mul_le_mul_of_nonneg_left hmod h2).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h1) hC)

/-- The fixed original radius pays the background's linear-in-parameter
coefficient in both original norms. The sharper C * norm u remainder is
retained separately in the native Hessian and value estimates. -/
def probesBackgroundNormConstant (n N : ℕ) (C radius : ℝ) : ℝ :=
  (probeAtlasFromNativeConstant n N 1 + probeAtlasFromNativeConstant n N 2) * (C*radius)

theorem probesBackgroundNormConstant_nonneg (n N : ℕ) {C radius : ℝ}
    (hC : 0 ≤ C) (hradius : 0 ≤ radius) :
    0 ≤ probesBackgroundNormConstant n N C radius := by
  exact mul_nonneg (add_nonneg (probeAtlasFromNativeConstant_nonneg n N 1)
    (probeAtlasFromNativeConstant_nonneg n N 2)) (mul_nonneg hC hradius)

theorem probes_background_norm_coefficients (n N : ℕ)
    {X : Type*} [SeminormedAddCommGroup X] {C radius : ℝ}
    (hC : 0 ≤ C) (u : X) (hu : ‖u‖ ≤ radius) :
    probeAtlasFromNativeConstant n N 1 * (C*‖u‖) ≤
      probesBackgroundNormConstant n N C radius ∧
    probeAtlasFromNativeConstant n N 2 * (C*‖u‖) ≤
      probesBackgroundNormConstant n N C radius := by
  have h1 := probeAtlasFromNativeConstant_nonneg n N 1
  have h2 := probeAtlasFromNativeConstant_nonneg n N 2
  have hbound := mul_le_mul_of_nonneg_left hu hC
  have hCr : 0 ≤ C*radius := mul_nonneg hC ((norm_nonneg u).trans hu)
  constructor
  · exact (mul_le_mul_of_nonneg_left hbound h1).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h2) hCr)
  · exact (mul_le_mul_of_nonneg_left hbound h2).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h1) hCr)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.probesCommonThreshold_pos
#print axioms GlobalEmbedding.Continuation.probesCommonThreshold_conditions
#print axioms GlobalEmbedding.Continuation.probes_secondary_modulus_le_cost
#print axioms GlobalEmbedding.Continuation.probes_secondary_norm_coefficients
#print axioms GlobalEmbedding.Continuation.probes_background_norm_coefficients
