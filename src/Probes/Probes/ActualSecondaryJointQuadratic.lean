import Probes.ActualSecondaryJointMode
import GlobalEmbedding.Paper.IncrementsSecondaryQuadraticForcing
import Probes.ActualSecondaryModulation
import Probes.ActualSecondarySupport

/-!
# Actual quadratic secondary modes with all joint jets

The same four signed, ordered physical quadratic coefficients used by the
original cancellation feed the original finite mode solver. Unlike the
original slice endpoint, the map, geometry, forcing, finite solution, full
reconstruction and reduced residual below all retain the parameter variable
inside their native iterated derivatives. The constant precedes the actual
label/subordinate families and the scales. No supplied forcing or solution
bound is an input.
-/

noncomputable section
open Manifold Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

theorem actual_joint_secondary_quadratic_mode_bounds
    (p j n : ℕ) (hbudget : j + 1 + p ≤ n) (MD : ℝ) (hMD : 0 ≤ MD) :
    ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ {Ep Label Sub : Type*} [Fintype Sub]
        [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
        (F : Ep → M → V) (hF : ∀ a, ContMDiff I 𝓘(ℝ, V) ∞ (F a))
        (c : Ep → D → M)
        (O S : Set (Ep × D)) (hO : IsOpen O) (hSO : S ⊆ O)
        (ell tau Mg delta : ℝ)
        (phi : Label → Ep → D → ℝ) (chi : Label → Ep → Sub → D → ℝ)
        (P Q : Label → Ep → Sub → D → V) (nu mu : Label) (q : Fin 4)
        (hnu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z nu) O)
        (hmu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z mu) O)
        (hnub : ∀ r ≤ n, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
          (fun w => incrementsSecondaryPhysicalCoefficient
            phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) w nu) z‖ ≤ MD * |delta|)
        (hmub : ∀ r ≤ n, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
          (fun w => incrementsSecondaryPhysicalCoefficient
            phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) w mu) z‖ ≤ MD * |delta|)
        (hBR : ContDiffOn ℝ ∞ (fun z : Ep × D => fun i =>
          (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
        (hJ : ContDiffOn ℝ ∞ (fun z : Ep × D =>
          (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
            (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
        (hG : ContDiffOn ℝ ∞ (fun z : Ep × D =>
          freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
        (hT : ContDiffOn ℝ ∞ (fun z : Ep × D =>
          incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
        (hA : ContDiffOn ℝ ∞ (fun z : Ep × D =>
          incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
        (hB : ContDiffOn ℝ ∞ (fun z : Ep × D =>
          incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
        (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
        (hMg : 0 ≤ Mg)
        (hBRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
          (fun w : Ep × D => fun a =>
            (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ Mg)
        (hJb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
          (fun w : Ep × D => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
            (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
        (hGb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
          (fun w : Ep × D => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
        (hTb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
          (fun w : Ep × D => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
        (hAb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
          (fun w : Ep × D => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
        (hBb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
          (fun w : Ep × D => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
        (Mphase : ℝ)
        (hphase : ContDiffOn ℝ ∞ (incrementsSecondaryQuadraticPhase phi nu mu q) O)
        (hphaseb : ∀ a < j, ∀ z ∈ S, ell ^ a * ‖iteratedFDeriv ℝ (a + 1)
          (incrementsSecondaryQuadraticPhase phi nu mu q) z‖ ≤ Mphase),
      let h := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) nu mu q
      let hR := fun z i a => (h z i a).re
      let hI := fun z i a => (h z i a).im
      let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
        ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mg * Mg *
          ‖incrementsModeTransverseSourceCLM (m := m)‖
      let K0 := 2 * ‖incrementsModeComplexInclude (m := m)‖ * Ck * CH
      let Profile := ∑ a ∈ Finset.range p, (2 * 2 ^ n * Mg) ^ a
      let CR := 2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg *
        max Mg ‖incrementsModeTransverseJet (m := m)‖
      let CZh := (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖) / 2
      let k := fun z : Ep × D => incrementsModeComplexInclude
        (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
        Complex.I • incrementsModeComplexInclude
          (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2)
      let U := fun a => incrementsActualModeSum
        (incrementsModeComplexFirstOrderA (F a) (hF a) (c a))
        (incrementsModeComplexFirstOrderB (F a) (hF a) (c a)) ((tau : ℂ) / Complex.I) p
        (fun x => k (a, x))
      let ZR := fun z : Ep × D => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
        (incrementsModeRealPart ∘ U z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2
      let ZI := fun z : Ep × D => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
        (incrementsModeImagPart ∘ U z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2
      let CZR := CR * ‖incrementsModeRealPart (m := m)‖ * K0 * Profile + CZh * CH
      let CZI := CR * ‖incrementsModeImagPart (m := m)‖ * K0 * Profile + CZh * CH
      let CW := euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j Mphase * (CZR + CZI)
      let wave := actualSecondaryModulation (incrementsSecondaryQuadraticPhase phi nu mu q) tau ZR ZI
      ContDiffOn ℝ ∞ (fun z : Ep × D => U z.1 z.2) O ∧
        ContDiffOn ℝ ∞ ZR O ∧ ContDiffOn ℝ ∞ ZI O ∧
        (∀ r ≤ j + 1, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
          (fun w : Ep × D => U w.1 w.2) z‖ ≤ tau * K0 * Profile * delta ^ 2) ∧
        (∀ r, r + p ≤ n → ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
          (fun w : Ep × D => ((tau : ℂ) / Complex.I)⁻¹ • U w.1 w.2 +
            incrementsModeComplexReducedOperator (F w.1) (hF w.1) (c w.1) (U w.1) w.2 - k w) z‖ ≤
            (2 * 2 ^ n * Mg) ^ p * (tau / ell) ^ p * K0 * delta ^ 2) ∧
        (∀ r ≤ j, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r ZR z‖ ≤
          (CR * ‖incrementsModeRealPart (m := m)‖ * K0 * Profile + CZh * CH) * delta ^ 2) ∧
        (∀ r ≤ j, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r ZI z‖ ≤
          (CR * ‖incrementsModeImagPart (m := m)‖ * K0 * Profile + CZh * CH) * delta ^ 2) ∧
        ContDiffOn ℝ ∞ wave O ∧
        (∀ r ≤ j, ∀ z ∈ S, tau ^ r * ‖iteratedFDeriv ℝ r wave z‖ ≤ CW * delta ^ 2) ∧
        tsupport wave ⊆
          tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) z nu) ∩
          tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) z mu) := by
  classical
  obtain ⟨CH, hCH, hdata⟩ := increments_secondary_quadratic_forcing_data n N MD hMD
  refine ⟨CH, hCH, ?_⟩
  intro Ep Label Sub _ _ _ F hF c O S hO hSO ell tau Mg delta phi chi P Q nu mu q
    hnu hmu hnub hmub hBR hJ hG hT hA hB hell hell1 htau htaul hMg
    hBRb hJb hGb hTb hAb hBb Mphase hphase hphaseb h hR hI Ck K0 Profile CR CZh k U ZR ZI
    CZR CZI CW wave
  obtain ⟨hhr, hhi, _hsym, hsuppR, hsuppI, hhrb, hhib⟩ :=
    hdata phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) nu mu q
      O S hO hSO ell delta hell hnu hmu hnub hmub
  have hKh : 0 ≤ CH * delta ^ 2 := mul_nonneg hCH (sq_nonneg delta)
  obtain ⟨hU, hZR, hZI, hUb, hEb, hZRb, hZIb⟩ :=
    actual_joint_secondary_mode_bounds F hF c hR hI n p j hbudget O S hO hSO
      hBR hJ hG hT hA hB hhr hhi ell tau Mg (CH * delta ^ 2) (CH * delta ^ 2)
      hell hell1 htau htaul hMg hKh hKh hBRb hJb hGb hTb hAb hBb hhrb hhib
  have hRb : ∀ r ≤ j, ∀ z ∈ S,
      ell ^ r * ‖iteratedFDeriv ℝ r ZR z‖ ≤ CZR * delta ^ 2 := by
    intro r hr z hz
    convert hZRb r hr z hz using 1 <;> dsimp only [CZR, K0, Ck, Profile, CR, CZh] <;> ring
  have hIb : ∀ r ≤ j, ∀ z ∈ S,
      ell ^ r * ‖iteratedFDeriv ℝ r ZI z‖ ≤ CZI * delta ^ 2 := by
    intro r hr z hz
    convert hZIb r hr z hz using 1 <;> dsimp only [CZI, K0, Ck, Profile, CR, CZh] <;> ring
  refine ⟨hU, hZR, hZI, ?_, ?_, hRb, hIb, ?_, ?_, ?_⟩
  · intro r hr z hz
    convert hUb r hr z hz using 1 <;> dsimp only [K0, Ck, Profile] <;> ring
  · intro r hr z hz
    convert hEb r hr z hz using 1 <;> dsimp only [K0, Ck] <;> ring
  · exact actualSecondaryModulation_contDiffOn _ tau ZR ZI O hphase hZR hZI
  · have hCZR : 0 ≤ CZR := by dsimp [CZR, CR, K0, Ck, Profile, CZh]; positivity
    have hCZI : 0 ≤ CZI := by dsimp [CZI, CR, K0, Ck, Profile, CZh]; positivity
    have hwb := actualSecondaryModulation_weighted_jets j
      (incrementsSecondaryQuadraticPhase phi nu mu q) ZR ZI O S hO hSO hphase hZR hZI
      tau ell Mphase (CZR * delta ^ 2) (CZI * delta ^ 2) htau htaul hell1
      (mul_nonneg hCZR (sq_nonneg delta)) (mul_nonneg hCZI (sq_nonneg delta)) hphaseb hRb hIb
    intro r hr z hz
    convert hwb r hr z hz using 1 <;> dsimp only [CW] <;> ring
  · have hchannels := actual_joint_secondary_channels_tsupport F hF c hR hI p tau
    exact ((actualSecondaryModulation_tsupport _ tau ZR ZI).trans
      (Set.union_subset hchannels.1 hchannels.2)).trans (Set.union_subset hsuppR hsuppI)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_secondary_quadratic_mode_bounds
