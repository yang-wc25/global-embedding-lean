import NormalPolar.ActualProbeInitialSupplyTensor
import Probes.Round4ParameterProbeFirstDefect
import Smoothing.ParameterRound2MeanGermResidualScaling

/-!
# The same physical error and normalized first defect on the original P

This is the algebra between the genuine mean and remainder producers and the
actual closed-state entrance. Its parameter space is the original arbitrary
P. The mean used in the remainder is exactly the same tensor whose defect is
supplied by the forced background construction. Every chart, sample and norm
is kept. These intermediate algebra lemmas do not assert an original-input
construction from already estimated errors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N count : ℕ} {M P : Type*} [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem actualProbeInitialSupply_same_mean_error_split
    (F U : P × M → V)
    (physicalMean H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (delta : ℝ) :
    incrementsOriginalMetricError F U H delta =
      incrementsOriginalMetricError F U physicalMean 1 + (physicalMean-delta^2 • H) := by
  funext p x
  simp only [incrementsOriginalMetricError,one_pow,one_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  abel

theorem actualProbeInitialSupply_same_mean_germ_add
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F U : P × M → V)
    (physicalMean : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (j q : ℕ) (delta tau ell CR CM : ℝ)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (htau : 0 < tau)
    (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hCM : 0 ≤ CM)
    (Rest Mean : parameterRound2_originalTensorGermSpace A B S W)
    (hRest : Rest.val = incrementsOriginalMetricError F U physicalMean 1)
    (hMean : Mean.val = physicalMean-delta^2 • H)
    (hRestBound : parameterRound2_originalTensorGermSeminorm A B S W hS hSO tau j Rest ≤
      CR*(delta*(tau/ell)^q+delta^3/tau))
    (hMeanBound : parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell j Mean ≤
      delta^2*((tau/ell)^(q+1)*CM)) :
    ∃ error : parameterRound2_originalTensorGermSpace A B S W,
      error.val = incrementsOriginalMetricError F U H delta ∧
      parameterRound2_originalTensorGermSeminorm A B S W hS hSO tau j error ≤
        (CR+CM)*(delta*(tau/ell)^q+delta^3/tau) := by
  let error := Rest+Mean
  have heq : error.val = incrementsOriginalMetricError F U H delta := by
    change Rest.val+Mean.val = _
    rw [hRest,hMean]
    exact (actualProbeInitialSupply_same_mean_error_split F U physicalMean H delta).symm
  have hMeanFast : parameterRound2_originalTensorGermSeminorm A B S W hS hSO tau j Mean ≤
      delta^2*((tau/ell)^(q+1)*CM) := by
    exact (ENNReal.toReal_mono
      (parameterRound2_tensorGerm_weighted_finite A B S W hS hSO Mean 0 j ell)
      (parameterRound2_paperAtlasWeighted_mono_scale 0 j tau ell htaul
        (incrementsOriginalTensorCoordinates A B Mean.val) (incrementsOriginalDifferentiation A B) S)).trans hMeanBound
  have hell : 0 < ell := htau.trans_le htaul
  have hd1 : delta ≤ 1 := hdeltatau.trans (htaul.trans hell1)
  have hratio : 0 ≤ tau/ell := div_nonneg htau.le hell.le
  have hratio1 : tau/ell ≤ 1 := (div_le_one hell).2 htaul
  have hMeanAbsorb : delta^2*((tau/ell)^(q+1)*CM) ≤ CM*(delta*(tau/ell)^q+delta^3/tau) := by
    have hsquare : delta^2 ≤ delta := by nlinarith
    have hp : (tau/ell)^(q+1) ≤ (tau/ell)^q := pow_le_pow_of_le_one hratio hratio1 (by omega)
    calc
      _ = CM*delta^2*(tau/ell)^(q+1) := by ring
      _ ≤ CM*delta*(tau/ell)^q := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hCM (show 0 ≤ delta^3/tau by positivity)]
  refine ⟨error,heq,?_⟩
  exact ((map_add_le_add (parameterRound2_originalTensorGermSeminorm A B S W hS hSO tau j) Rest Mean).trans
    (add_le_add hRestBound (hMeanFast.trans hMeanAbsorb))).trans_eq (by ring)

theorem actualProbeInitialSupply_normalize_produced_error
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F0 U : P × M → V) (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
    (delta delta1 : ℝ) (hdelta : delta ≠ 0) (hdelta1 : delta1 ≠ 0) (hsmall : delta^2 ≤ 1)
    (error : parameterRound2_originalTensorGermSpace A B S W)
    (herror : error.val = incrementsOriginalMetricError
      (fun z => Real.sqrt (1-delta^2) • F0 z) U
      (fun p x => (1-(delta1/delta)^2) • inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) delta)
    (weight C : ℝ) (j : ℕ)
    (hbound : parameterRound2_originalTensorGermSeminorm A B S W hS hSO weight j error ≤ C) :
    ∃ normalized : parameterRound2_originalTensorGermSpace A B S W,
      normalized.val = (fun p x => (delta1^2)⁻¹ •
        (inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x-
          inducedMetric (I := 𝓙) (fun y => Real.sqrt (1-delta^2) • F0 (p,y)+U (p,y)) x)-
        inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) ∧
      parameterRound2_originalTensorGermSeminorm A B S W hS hSO weight j normalized ≤ (delta1^2)⁻¹*C := by
  let normalized := -(delta1^2)⁻¹ • error
  refine ⟨normalized,?_,?_⟩
  · change -(delta1^2)⁻¹ • error.val = _
    rw [herror]
    exact (round4ParameterProbe_first_normalized_defect F0 hF0 U delta delta1 hdelta hdelta1 hsmall).symm
  · change (parameterRound2_originalTensorGermSeminorm A B S W hS hSO weight j)
      (-(delta1^2)⁻¹ • error) ≤ _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg delta1))]
    exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (sq_nonneg delta1))

/-- The actual original-scale error is normalized against exactly the same
first map. This retains arbitrary P and yields the two literal entrance powers. -/
theorem actualProbeInitialSupply_normalized_original_scale
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F0 U : P × M → V) (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
    (C t : ℝ) (j : ℕ) (ht : 0 < t) (ht1 : t ≤ 1)
    (error : parameterRound2_originalTensorGermSpace A B S W)
    (herror : error.val = incrementsOriginalMetricError
      (fun z => Real.sqrt (1-(t^10)^2) • F0 z) U
      (fun p x => (1-((t^((6 : ℝ)/5))^10/(t^10))^2) •
        inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) (t^10))
    (hbound : parameterRound2_originalTensorGermSeminorm A B S W hS hSO (t^((6 : ℝ)/5)) j error ≤
      C*(t^10*(t^((6 : ℝ)/5)/t^((11 : ℝ)/10))^440+(t^10)^3/t^((6 : ℝ)/5))) :
    ∃ normalized : parameterRound2_originalTensorGermSpace A B S W,
      normalized.val = (fun p x => (((t^((6 : ℝ)/5))^10)^2)⁻¹ •
        (inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x-
          inducedMetric (I := 𝓙) (fun y => Real.sqrt (1-(t^10)^2) • F0 (p,y)+U (p,y)) x)-
        inducedMetric (I := 𝓙) (fun y => F0 (p,y)) x) ∧
      parameterRound2_originalTensorGermSeminorm A B S W hS hSO (t^((6 : ℝ)/5)) j normalized ≤
        C*(t^(30 : ℝ)+t^((24 : ℝ)/5)) := by
  have hsmall : (t^10)^2 ≤ 1 := pow_le_one₀ (pow_nonneg ht.le _) (pow_le_one₀ ht.le ht1)
  obtain ⟨normalized,hvalue,hnorm⟩ := actualProbeInitialSupply_normalize_produced_error
    A B S W hS hSO F0 U hF0 (t^10) ((t^((6 : ℝ)/5))^10)
    (ne_of_gt (pow_pos ht _)) (ne_of_gt (pow_pos (Real.rpow_pos_of_pos ht _) _)) hsmall
    error herror (t^((6 : ℝ)/5))
    (C*(t^10*(t^((6 : ℝ)/5)/t^((11 : ℝ)/10))^440+(t^10)^3/t^((6 : ℝ)/5))) j hbound
  refine ⟨normalized,hvalue,hnorm.trans_eq ?_⟩
  calc
    _ = C*((((t^((6 : ℝ)/5))^10)^2)⁻¹*
        (t^10*(t^((6 : ℝ)/5)/t^((11 : ℝ)/10))^440+(t^10)^3/t^((6 : ℝ)/5))) := by ring
    _ = _ := congrArg (fun x : ℝ => C*x) (round4ParameterProbe_first_error_scale_identity ht)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_same_mean_germ_add
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_normalize_produced_error

#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_same_mean_error_split
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_normalized_original_scale
