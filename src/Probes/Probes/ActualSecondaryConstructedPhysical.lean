import Probes.ActualSecondaryConstructedPiece
import Probes.ActualSecondaryRealPhysicalIdentity
import Probes.ActualSecondarySplitScalePhysical

/-!
# Physical tensor budget for the same constructed secondary piece

Primitive data for the already constructed wave now supplies its actual
physical tensor residual. The finite source estimate and finite solver error
are derived internally, then remodulated and assembled in the native tensor
norm. In particular, no small physical error or smooth residual is an input.
-/

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

private local instance physicalCostTensorSemi (m : ℕ) : SeminormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance physicalCostTensorNormed (m : ℕ) : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance physicalCostTensorSpace (m : ℕ) : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def actualSecondaryPhysicalCost (m N n length j : ℕ) (Mg CH : ℝ) : ℝ :=
  let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n+n) *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mg * Mg *
      ‖incrementsModeTransverseSourceCLM (m := m)‖
  ‖parameterRound2_meanTensorAssembly (m+1)‖ * incrementsFastMultiplierConstant j 1 *
    (4 * (2 * 2 ^ n * Mg) ^ length * ‖incrementsModeComplexInclude (m := m)‖ * Ck * CH)

theorem actualSecondaryPhysicalCost_nonneg (m N n length j : ℕ) (Mg CH : ℝ)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) :
    0 ≤ actualSecondaryPhysicalCost m N n length j Mg CH := by
  have hc := (incrementsFastMultiplierConstant_pos j 1).le
  unfold actualSecondaryPhysicalCost
  positivity

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)

private local instance constructedTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance constructedTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance constructedTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_constructed_secondary_physical_tensor_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (d : ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (chart : Ep → OpenPartialHomeomorph M D) (hc : d.c = fun p x => (chart p).symm x)
    (hchart : ∀ p, chart p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hOt : ∀ z ∈ d.chart.target, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ d.chart.target,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((chart z.1).symm z.2)))
    (hfree : ∀ z ∈ d.chart.target,
      let β := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ)
      (β.comp β.adjoint).IsInvertible)
    (hRsymm : ∀ z ∈ d.chart.target, ∀ i j, d.hR z i j = d.hR z j i)
    (hIsymm : ∀ z ∈ d.chart.target, ∀ i j, d.hI z i j = d.hI z j i)
    (tau : ℝ) (length : ℕ) (hbudget : j + length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) :
    let B := actualRemodulatedPhysicalTensor
      (actualSecondaryPhysicalError F hF chart d.hR d.hI tau length) (fun z : X => z.2 0) tau
    ContDiffOn ℝ ∞ B d.chart.target ∧
      ∀ s ≤ j, ∀ z ∈ d.sample, tau ^ s * ‖iteratedFDeriv ℝ s B z‖ ≤
        actualSecondaryPhysicalCost m N n length j Mg CH * (tau / ell) ^ length * delta ^ 2 := by
  intro B
  have hBR := d.brows_smooth
  have hJ := d.transverse_smooth
  have hA := d.coefficientA_smooth
  have hBb := d.coefficientB_smooth
  have hbBR := d.brows_bound
  have hbJ := d.transverse_bound
  have hbA := d.coefficientA_bound
  have hbB := d.coefficientB_bound
  have hcp : ∀ p, d.c p = ((chart p).symm : D → M) := fun p => congrFun hc p
  rw [hc] at hBR hJ hA hBb hbBR hbJ hbA hbB
  obtain ⟨he, heb⟩ := actual_secondary_physical_error_split_scale_jets F hF chart hchart
    d.chart.target d.sample d.chart.open_target d.sample_subset hOt hinj hfree d.hR d.hI
    d.forcingR_smooth d.forcingI_smooth hRsymm hIsymm hBR hJ hA hBb n length tau ell Mg
    (CH * delta ^ 2) (CH * delta ^ 2) htau hell hell1 hMg (by positivity) (by positivity)
    hbBR hbJ hbA hbB d.forcingR_bound d.forcingI_bound
  let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n+n) *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mg * Mg *
      ‖incrementsModeTransverseSourceCLM (m := m)‖
  let Ke := 2 * ((2 * 2 ^ n * Mg) ^ length * (tau / ell) ^ length *
    (‖incrementsModeComplexInclude (m := m)‖ * Ck * (CH * delta ^ 2 + CH * delta ^ 2)))
  have hKe : 0 ≤ Ke := by dsimp [Ke, Ck]; positivity
  let phase : X →L[ℝ] ℝ := actualSecondaryCoordinatePhase
  have hphase : ContDiffOn ℝ ∞ (fun z : X => z.2 0) d.chart.target := phase.contDiff.contDiffOn
  have hphaseb : ∀ s < j, ∀ z ∈ d.sample,
      ell ^ s * ‖iteratedFDeriv ℝ (s+1) (fun y : X => y.2 0) z‖ ≤ 1 := by
    intro s _ z _
    exact actual_linear_phase_slow_jets phase actualSecondaryCoordinatePhase_norm_le ell z s
  obtain ⟨hB, hb⟩ := actual_remodulated_physical_tensor_weighted_jets
    (actualSecondaryPhysicalError F hF chart d.hR d.hI tau length) (fun z : X => z.2 0)
    d.chart.target d.sample d.chart.open_target d.sample_subset he hphase j tau ell 1 Ke
    htau htaul hell1 hKe hphaseb (fun s hs z hz => heb s (by omega) z hz)
  refine ⟨hB, ?_⟩
  intro s hs z hz
  exact (hb s hs z hz).trans_eq (by dsimp only [Ke, Ck, actualSecondaryPhysicalCost]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_constructed_secondary_physical_tensor_jets
