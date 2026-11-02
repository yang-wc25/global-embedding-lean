import Probes.ActualSecondaryForcedWave
import Probes.ActualSecondarySplitScaleMode

/-! The same constructed inhomogeneous wave with the genuine adapted scale:
A/G/J/trueBrow have shift zero; value coefficient B and T0 have shift one.
The original wave, constants and delta squared budget are unchanged. -/

noncomputable section
open Manifold Set Filter GlobalEmbedding.Paper
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

theorem actual_secondary_forced_wave_split_scale_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (n length j : ℕ) (hbudget : j + 1 + length ≤ n)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (ell tau Mg CH delta : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH)
    (hBRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => fun a => (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ Mg)
    (hJb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hGb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ i ≤ j, ∀ z ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hAb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ i ≤ n, ∀ z ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hhRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hR z‖ ≤ CH * delta ^ 2)
    (hhIb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hI z‖ ≤ CH * delta ^ 2) :
    ContDiffOn ℝ ∞ (actualSecondaryWave F hF c hR hI (fun z => z.2 0) tau length) O ∧
      (∀ r ≤ j, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r
        (actualSecondaryWave F hF c hR hI (fun z => z.2 0) tau length) z‖ ≤
          actualSecondaryForcedWaveCost m N n length j Mg CH * delta ^ 2) ∧
      tsupport (actualSecondaryWave F hF c hR hI (fun z => z.2 0) tau length) ⊆
        tsupport hR ∪ tsupport hI := by
  let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mg * Mg *
      ‖incrementsModeTransverseSourceCLM (m := m)‖
  let K0 := 2 * ‖incrementsModeComplexInclude (m := m)‖ * Ck * CH
  let profile := ∑ a ∈ Finset.range length, (2 * 2 ^ n * Mg) ^ a
  let CR := 2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg * max Mg ‖incrementsModeTransverseJet (m := m)‖
  let CZh := (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖) / 2
  let KR := CR * ‖incrementsModeRealPart (m := m)‖ * K0 * profile + CZh * CH
  let KI := CR * ‖incrementsModeImagPart (m := m)‖ * K0 * profile + CZh * CH
  have hKR : 0 ≤ KR := by dsimp [KR, CR, K0, Ck, profile, CZh]; positivity
  have hKI : 0 ≤ KI := by dsimp [KI, CR, K0, Ck, profile, CZh]; positivity
  obtain ⟨_hU, hZR, hZI, _hUb, _hEb, hZRb, hZIb⟩ := actual_joint_secondary_mode_split_scale_bounds
    F hF c hR hI n length j hbudget O S hO hSO hBR hJ hG hT hA hB hhR hhI
    ell tau Mg (CH * delta ^ 2) (CH * delta ^ 2) hell hell1 htau htaul hMg
    (by positivity) (by positivity) hBRb hJb hGb hTb hAb hBb hhRb hhIb
  let ZR := actualSecondaryRealChannel F hF c hR hI tau length
  let ZI := actualSecondaryImagChannel F hF c hR hI tau length
  have hRb : ∀ r ≤ j, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r ZR z‖ ≤ KR * delta ^ 2 := by
    intro r hr z hz
    have hb := hZRb r hr z hz
    change ell ^ r * ‖iteratedFDeriv ℝ r ZR z‖ ≤ _ at hb
    convert hb using 1 <;> dsimp only [KR, CR, K0, Ck, profile, CZh] <;> ring
  have hIb : ∀ r ≤ j, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r ZI z‖ ≤ KI * delta ^ 2 := by
    intro r hr z hz
    have hb := hZIb r hr z hz
    change ell ^ r * ‖iteratedFDeriv ℝ r ZI z‖ ≤ _ at hb
    convert hb using 1 <;> dsimp only [KI, CR, K0, Ck, profile, CZh] <;> ring
  let phase : X →L[ℝ] ℝ := actualSecondaryCoordinatePhase
  have hphase : ContDiffOn ℝ ∞ (fun z : X => z.2 0) O := phase.contDiff.contDiffOn
  have hphaseb : ∀ a < j, ∀ z ∈ S,
      ell ^ a * ‖iteratedFDeriv ℝ (a + 1) (fun w : X => w.2 0) z‖ ≤ 1 := by
    intro a _ z _
    exact actual_linear_phase_slow_jets phase actualSecondaryCoordinatePhase_norm_le ell z a
  have hwb := actualSecondaryModulation_weighted_jets j (fun z : X => z.2 0) ZR ZI O S hO hSO
    hphase hZR hZI tau ell 1 (KR * delta ^ 2) (KI * delta ^ 2)
    htau htaul hell1 (by positivity) (by positivity) hphaseb hRb hIb
  refine ⟨actualSecondaryModulation_contDiffOn _ tau ZR ZI O hphase hZR hZI, ?_, ?_⟩
  · intro r hr z hz
    change tau ^ r * ‖iteratedFDeriv ℝ r
      (actualSecondaryModulation (fun z : X => z.2 0) tau ZR ZI) z‖ ≤ _
    convert hwb r hr z hz using 1 <;>
      dsimp only [actualSecondaryForcedWaveCost, KR, KI, CR, K0, Ck, profile, CZh] <;> ring
  · have hs := actual_joint_secondary_channels_tsupport F hF c hR hI length tau
    exact (actualSecondaryModulation_tsupport _ tau ZR ZI).trans (Set.union_subset hs.1 hs.2)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_forced_wave_split_scale_jets
