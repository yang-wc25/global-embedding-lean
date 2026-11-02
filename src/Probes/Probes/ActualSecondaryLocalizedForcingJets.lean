import Probes.ActualSecondaryForcingPullback
import Probes.ActualSecondaryGlobalPhysicalSum

/-!
# Actual inverse-chart tensor localization of the negative forcing

The h entering the original finite solver is the original tensor composed
with the actual inverse chart, evaluated on both genuine spatial Jacobians,
and multiplied by the ordinary subordinate cutoff. Its joint derivative
budget is derived here. No bound for the localized forcing is an input.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ

private local instance localForceTensorSemi : SeminormedAddCommGroup Tensor :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance localForceTensorNormed : NormedAddCommGroup Tensor :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance localForceTensorSpace : NormedSpace ℝ Tensor :=
  ContinuousLinearMap.toNormedSpace

private def actualTensorBasisLinear : Tensor →ₗ[ℝ] Source where
  toFun := actualTensorBasisCoefficients
  map_add' H K := by ext i j; rfl
  map_smul' a H := by ext i j; rfl

theorem actualTensorBasisCoefficients_norm_le (H : Tensor) :
    ‖actualTensorBasisCoefficients H‖ ≤ ‖H‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg H)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg H)).2
  intro j
  change ‖H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ ≤ ‖H‖
  calc
    _ ≤ ‖H (EuclideanSpace.single i 1)‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
      (H (EuclideanSpace.single i 1)).le_opNorm _
    _ ≤ (‖H‖ * ‖EuclideanSpace.single i (1 : ℝ)‖) * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
      mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
    _ = _ := by simp [EuclideanSpace.single, PiLp.norm_single]

def actualTensorBasisCLM : Tensor →L[ℝ] Source :=
  actualTensorBasisLinear.mkContinuous 1 fun H => by
    change ‖actualTensorBasisCoefficients H‖ ≤ 1 * ‖H‖
    simpa only [one_mul] using actualTensorBasisCoefficients_norm_le H

theorem actualTensorBasisCLM_norm_le : ‖actualTensorBasisCLM (m := m)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro H
  change ‖actualTensorBasisCoefficients H‖ ≤ 1 * ‖H‖
  simpa only [one_mul] using actualTensorBasisCoefficients_norm_le H

@[simp] theorem actualTensorBasisCLM_apply (H : Tensor) :
    actualTensorBasisCLM H = actualTensorBasisCoefficients H := rfl

/-- Smoothness uses the genuine spatial derivative, not an auxiliary frame. -/
theorem actual_secondary_inverse_forcing_contDiffOn
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hc : ContDiffOn ℝ ∞ cutoff e.source) (hH : ContDiffOn ℝ ∞ H e.source) :
    ContDiffOn ℝ ∞ (actualSecondaryInverseForcing e cutoff H) e.target := by
  let P : X →L[ℝ] D := ContinuousLinearMap.snd ℝ Ep D
  have hs : ContDiffOn ℝ ∞ (P ∘ e.symm) e.target := P.contDiff.comp_contDiffOn he
  have hJ : ContDiffOn ℝ ∞ (actualJointSpatialJacobian e.symm) e.target :=
    (incrementsJointSpatialJets_bridge (P ∘ e.symm) e.target e.open_target hs).2.1
  have hB := hH.comp he e.symm.mapsTo
  have hpull : ContDiffOn ℝ ∞ (fun z => (H (e.symm z)).bilinearComp
      (actualJointSpatialJacobian e.symm z) (actualJointSpatialJacobian e.symm z)) e.target := by
    let flip : Tensor ≃ₗᵢ[ℝ] Tensor := ContinuousLinearMap.flipₗᵢ ℝ D D ℝ
    have h1 := hB.clm_comp hJ
    have h2 := (flip.contDiff.comp_contDiffOn h1).clm_comp hJ
    exact flip.contDiff.comp_contDiffOn h2
  exact actualTensorBasisCLM.contDiff.comp_contDiffOn ((hc.comp he e.symm.mapsTo).smul hpull)

/-- A scale-free localization constant, before every actual chart and field. -/
def actualSecondaryLocalizationCost (T : ℕ → ℝ) (n : ℕ) (Kcut : ℝ) : ℝ :=
  2 ^ n * actualFastChartTransferPrefix T n * Kcut * actualFastTensorChartTransferPrefix T n

theorem actualSecondaryLocalizationCost_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (n : ℕ) (Kcut : ℝ) (hKcut : 0 ≤ Kcut) :
    0 ≤ actualSecondaryLocalizationCost T n Kcut := by
  have h1 := actualFastChartTransferPrefix_nonneg T hT n
  have h2 := actualFastTensorChartTransferPrefix_nonneg T hT n
  unfold actualSecondaryLocalizationCost
  positivity

theorem actual_secondary_inverse_forcing_weighted_jets
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (n : ℕ) (Kcut KH : ℝ)
    (hKcut : 0 ≤ Kcut) (hKH : 0 ≤ KH)
    (e : OpenPartialHomeomorph X X) (cutoff : X → ℝ) (H : X → Tensor)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hc : ContDiffOn ℝ ∞ cutoff e.source) (hH : ContDiffOn ℝ ∞ H e.source)
    (ell : ℝ) (hell : 0 < ell) (S : Set X) (hS : S ⊆ e.target)
    (hcut : ∀ i ≤ n, ∀ z ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i cutoff (e.symm z)‖ ≤ Kcut)
    (hHjet : ∀ i ≤ n, ∀ z ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i H (e.symm z)‖ ≤ KH)
    (hinv : ∀ i, 1 ≤ i → i ≤ n+1 → ∀ z ∈ S,
      ell ^ (i-1) * ‖iteratedFDeriv ℝ i e.symm z‖ ≤ T i) :
    ContDiffOn ℝ ∞ (actualSecondaryInverseForcing e cutoff H) e.target ∧
      ∀ k ≤ n, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
        (actualSecondaryInverseForcing e cutoff H) z‖ ≤
          actualSecondaryLocalizationCost T n Kcut * KH := by
  let c := cutoff ∘ e.symm
  let B : X → Tensor := fun z => (H (e.symm z)).bilinearComp
    (actualJointSpatialJacobian e.symm z) (actualJointSpatialJacobian e.symm z)
  have h1 := actualFastChartTransferPrefix_nonneg T hT n
  have h2 := actualFastTensorChartTransferPrefix_nonneg T hT n
  have hcs : ContDiffOn ℝ ∞ c e.target := hc.comp he e.symm.mapsTo
  refine ⟨actual_secondary_inverse_forcing_contDiffOn e cutoff H he hc hH, ?_⟩
  intro k hk z hz
  have hb := fun i (hi : i ≤ n) => actual_fast_joint_tensor_chart_transfer T hT i e.symm H
    e.target e.source e.open_target e.open_source he hH e.symm.mapsTo z (hS hz)
    ell ell KH hell le_rfl hKH (fun a ha => hHjet a (ha.trans hi) z hz)
    (fun a ha hai => hinv a ha (by omega) z hz)
  have hBs : ContDiffOn ℝ ∞ B e.target := (hb 0 (by omega)).1
  have hcb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i c z‖ ≤
      actualFastChartTransferPrefix T n * Kcut := by
    intro i hi
    have hh := actual_fast_joint_chart_transfer T hT i e.symm cutoff e.target e.source
      e.open_target e.open_source he hc e.symm.mapsTo z (hS hz) ell ell Kcut hell le_rfl
      (fun a ha => hcut a (by omega) z hz) (fun a ha hai => hinv a ha (by omega) z hz)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (actualFastChartTransferCost_le_prefix T hT (by omega)) hKcut)
  have hBb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i B z‖ ≤
      actualFastTensorChartTransferPrefix T n * KH := by
    intro i hi
    exact (hb i (by omega)).2.trans (mul_le_mul_of_nonneg_right
      (actualFastTensorChartTransferCost_le_prefix T hT (by omega)) hKH)
  have hprod := slow_bilinear_jet_bound (ContinuousLinearMap.lsmul ℝ ℝ (E := Tensor))
    ContinuousLinearMap.opNorm_lsmul_le e.target e.open_target c B hcs hBs k ell
    (actualFastChartTransferPrefix T n * Kcut) (actualFastTensorChartTransferPrefix T n * KH)
    hell.le (by positivity) z (hS hz) hcb hBb
  have hnorm := slow_linear_jet_bound actualTensorBasisCLM e.target e.open_target
    (fun y => c y • B y) (hcs.smul hBs) k ell
    (2 ^ k * (actualFastChartTransferPrefix T n * Kcut) *
      (actualFastTensorChartTransferPrefix T n * KH)) hell.le z (hS hz) hprod
  apply hnorm.trans
  calc
    _ ≤ 1 * (2 ^ k * (actualFastChartTransferPrefix T n * Kcut) *
        (actualFastTensorChartTransferPrefix T n * KH)) :=
      mul_le_mul_of_nonneg_right actualTensorBasisCLM_norm_le (by positivity)
    _ ≤ 1 * (2 ^ n * (actualFastChartTransferPrefix T n * Kcut) *
        (actualFastTensorChartTransferPrefix T n * KH)) := by gcongr; norm_num
    _ = _ := by unfold actualSecondaryLocalizationCost; ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualTensorBasisCLM_norm_le
#print axioms GlobalEmbedding.Continuation.actual_secondary_inverse_forcing_weighted_jets
