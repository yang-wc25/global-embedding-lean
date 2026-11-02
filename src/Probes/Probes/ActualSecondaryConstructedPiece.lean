import Probes.ActualSecondarySplitScaleWave
import Probes.ActualSecondaryLocalPhaseSupport

/-!
# Primitive data and the actual constructed secondary piece

The package below contains only original chart, forcing, support and geometric
input profiles. It contains no displacement, solution, residual, or requested
output estimate. Its wave is the literal source / finite polynomial solver /
inhomogeneous reconstruction / supported sine-cosine construction already
defined in the preceding files. A sampling set is retained explicitly; no
bound on an entire unbounded chart target is silently required. The genuine
adapted value coefficient B and T0 use shift one; the other profiles use shift zero.
-/

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

structure ActualSecondaryPieceData
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M)) where
  c : Ep → D → M
  hR : X → Source
  hI : X → Source
  chart : OpenPartialHomeomorph (Ep × M) X
  sample : Set X
  sample_subset : sample ⊆ chart.target
  support : Set (Ep × M)
  support_closed : IsClosed (Subtype.val ⁻¹' support : Set W)
  support_source : support ⊆ chart.source
  source_domain : chart.source ⊆ W
  chart_smooth : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, X) ∞ chart chart.source
  inverse : ∀ z ∈ chart.target, chart.symm z = (z.1, c z.1 z.2)
  phase : Ep × M → ℝ
  phase_smooth : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ phase chart.source
  adaptation : ∀ y ∈ chart.source, phase y = (chart y).2 0
  forcing_support : ∀ z ∈ chart.target,
    z ∈ tsupport hR ∪ tsupport hI → chart.symm z ∈ support
  brows_smooth : ContDiffOn ℝ ∞ (fun z : X => fun i =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) chart.target
  inverse_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) chart.target
  transverse_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) chart.target
  value_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    incrementsModeTransverseValue (F z.1) (c z.1) z.2) chart.target
  coefficientA_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) chart.target
  coefficientB_smooth : ContDiffOn ℝ ∞ (fun z : X =>
    incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) chart.target
  forcingR_smooth : ContDiffOn ℝ ∞ hR chart.target
  forcingI_smooth : ContDiffOn ℝ ∞ hI chart.target
  brows_bound : ∀ i ≤ n, ∀ z ∈ sample, ell ^ i * ‖iteratedFDeriv ℝ i
    (fun w : X => fun a => (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ Mg
  transverse_bound : ∀ i ≤ n, ∀ z ∈ sample, ell ^ i * ‖iteratedFDeriv ℝ i
    (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg
  inverse_bound : ∀ i ≤ j, ∀ z ∈ sample, ell ^ i * ‖iteratedFDeriv ℝ i
    (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg
  value_bound : ∀ i ≤ j, ∀ z ∈ sample, ell ^ (i+1) * ‖iteratedFDeriv ℝ i
    (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg
  coefficientA_bound : ∀ i ≤ n, ∀ z ∈ sample, ell ^ i * ‖iteratedFDeriv ℝ i
    (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg
  coefficientB_bound : ∀ i ≤ n, ∀ z ∈ sample, ell ^ (i+1) * ‖iteratedFDeriv ℝ i
    (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg
  forcingR_bound : ∀ i ≤ n, ∀ z ∈ sample,
    ell ^ i * ‖iteratedFDeriv ℝ i hR z‖ ≤ CH * delta ^ 2
  forcingI_bound : ∀ i ≤ n, ∀ z ∈ sample,
    ell ^ i * ‖iteratedFDeriv ℝ i hI z‖ ≤ CH * delta ^ 2

namespace ActualSecondaryPieceData

variable {F : Ep → M → EuclideanSpace ℝ (Fin N)}
  {hF : ∀ p, ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (F p)}
  {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}

def wave (d : ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) : Ep × M → V :=
  actualSecondarySupportedWave F hF d.c d.hR d.hI d.chart d.phase tau length

theorem wave_regular (d : ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hW : IsOpen W) :
    ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ (d.wave tau length) W ∧
      tsupport (fun y : W => d.wave tau length y) ⊆ Subtype.val ⁻¹' d.support := by
  exact actual_secondary_supported_wave_local_phase_regular F hF d.c d.hR d.hI length tau d.chart W hW
    d.source_domain d.support d.support_closed d.support_source
    d.chart_smooth d.inverse d.brows_smooth d.inverse_smooth d.transverse_smooth d.value_smooth
    d.coefficientA_smooth d.coefficientB_smooth d.forcingR_smooth d.forcingI_smooth
    d.forcing_support d.phase d.phase_smooth

theorem local_wave_jets (d : ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hbudget : j + 1 + length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) :
    ContDiffOn ℝ ∞ (actualSecondaryWave F hF d.c d.hR d.hI (fun z : X => z.2 0) tau length)
      d.chart.target ∧
      (∀ r ≤ j, ∀ z ∈ d.sample, tau ^ r * ‖iteratedFDeriv ℝ r
        (actualSecondaryWave F hF d.c d.hR d.hI (fun z : X => z.2 0) tau length) z‖ ≤
          actualSecondaryForcedWaveCost m N n length j Mg CH * delta ^ 2) := by
  have h := actual_secondary_forced_wave_split_scale_jets F hF d.c d.hR d.hI n length j hbudget
    d.chart.target d.sample d.chart.open_target d.sample_subset d.brows_smooth d.transverse_smooth
    d.inverse_smooth d.value_smooth d.coefficientA_smooth d.coefficientB_smooth
    d.forcingR_smooth d.forcingI_smooth ell tau Mg CH delta hell hell1 htau htaul hMg hCH
    d.brows_bound d.transverse_bound d.inverse_bound d.value_bound d.coefficientA_bound
    d.coefficientB_bound d.forcingR_bound d.forcingI_bound
  exact ⟨h.1, h.2.1⟩

theorem observation_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (d : ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hbudget : j + 1 + length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (kappa : Y → Ep × M) (O : Set Y) (hO : IsOpen O)
    (hsource : ∀ y ∈ O, kappa y ∈ d.chart.source)
    (htransition : ContDiffOn ℝ ∞ (d.chart ∘ kappa) O)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (y : Y) (hy : y ∈ O) (hsample : d.chart (kappa y) ∈ d.sample)
    (htransitionb : ∀ i, 1 ≤ i → i ≤ j →
      ell ^ (i - 1) * ‖iteratedFDeriv ℝ i (d.chart ∘ kappa) y‖ ≤ T i) :
    ContDiffOn ℝ ∞ (d.wave tau length ∘ kappa) O ∧
      tau ^ j * ‖iteratedFDeriv ℝ j (d.wave tau length ∘ kappa) y‖ ≤
        actualFastChartTransferCost T j * actualSecondaryForcedWaveCost m N n length j Mg CH * delta ^ 2 := by
  obtain ⟨hl, hb⟩ := d.local_wave_jets tau length hbudget hell hell1 htau htaul hMg hCH
  refine ⟨actual_secondary_supported_observation_contDiffOn F hF d.c d.hR d.hI d.chart d.phase
    (fun z : X => z.2 0) tau length kappa O hsource
    (fun y hy => d.adaptation (kappa y) (hsource y hy)) htransition hl, ?_⟩
  have h := actual_secondary_supported_observation_weighted_jets F hF d.c d.hR d.hI d.chart
    d.phase (fun z : X => z.2 0) tau ell length kappa O hO hsource
    (fun y hy => d.adaptation (kappa y) (hsource y hy)) htransition hl T hT j
    (actualSecondaryForcedWaveCost m N n length j Mg CH * delta ^ 2) htau htaul y hy
    (fun i hi => hb i hi _ hsample) htransitionb
  exact h.trans_eq (by ring)

end ActualSecondaryPieceData
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ActualSecondaryPieceData.wave_regular
#print axioms GlobalEmbedding.Continuation.ActualSecondaryPieceData.local_wave_jets
#print axioms GlobalEmbedding.Continuation.ActualSecondaryPieceData.observation_jets
