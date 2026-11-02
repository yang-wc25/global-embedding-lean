import NormalPolar.ActualRepairModelFirstDefectTotalCoordinates
import Probes.Round4ParameterProbeFirstDefect
import Smoothing.ParameterRound2MeanGermResidualScaling

/-! Exact same-array addition and normalization used by the producer-driven
first-step endpoint. The two inputs here are separately produced genuine
germs; this module is only the original-norm algebra between their producers
and the literal contracted first map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N count : ℕ} {M Label : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem actualRepairModelFirstDefect_same_array_germ_add
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F U : Ep × M → V) (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → V)
    (H : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (j q : ℕ) (delta tau ell CR CM : ℝ)
    (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau) (htau : 0 < tau)
    (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hCM : 0 ≤ CM)
    (Rest Mean : parameterRound2_originalTensorGermSpace A B S W)
    (hRest : Rest.val = actualRepairModelFirstDefectArrayRest F U phase tau R Q)
    (hMean : Mean.val = round4ParameterProbeArrayMean (I := 𝓙) phase tau R Q-delta^2 • H)
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
    exact (actualRepairModelFirstDefect_array_error_split F U phase tau R Q H delta).symm
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

theorem actualRepairModelFirstDefect_normalize_produced_error
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F0 U : Ep × M → V) (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
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

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_same_array_germ_add
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_normalize_produced_error
