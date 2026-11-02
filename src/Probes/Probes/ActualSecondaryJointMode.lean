import Probes.ActualSecondaryJointSource
import Probes.ActualJointFiniteResidual

/-!
# One actual secondary mode with all joint parameter/source jets

The forcing is passed to the original source, original finite polynomial and
original inhomogeneous reconstruction. The parameter-dependent geometry is
kept in the formulas. All mixed jets and the residual are estimated for these
same actual outputs; no supplied source, solution or residual bound is used.
-/

noncomputable section
open Manifold Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators

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
local notation "Cdata" => Fin (m + 1) → ℂ

theorem actual_joint_secondary_mode_bounds
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (n p j : ℕ) (hbudget : j + 1 + p ≤ n)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (ell tau Mg KhR KhI : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hKhR : 0 ≤ KhR) (hKhI : 0 ≤ KhI)
    (hBRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => fun a =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ Mg)
    (hJb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hGb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hAb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hhRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hR z‖ ≤ KhR)
    (hhIb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hI z‖ ≤ KhI) :
    let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
      ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mg * Mg *
        ‖incrementsModeTransverseSourceCLM (m := m)‖
    let Kc := ‖incrementsModeComplexInclude (m := m)‖ * Ck * (KhR + KhI)
    let Profile := ∑ a ∈ Finset.range p, (2 * 2 ^ n * Mg) ^ a
    let CR := 2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg *
      max Mg ‖incrementsModeTransverseJet (m := m)‖
    let CH := (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖) / 2
    let k := fun z : X => incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
      Complex.I • incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2)
    let U := fun a => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F a) (hF a) (c a))
      (incrementsModeComplexFirstOrderB (F a) (hF a) (c a)) ((tau : ℂ) / Complex.I) p
      (fun x => k (a, x))
    let ZR := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeRealPart ∘ U z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2
    let ZI := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeImagPart ∘ U z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2
    ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) O ∧
      ContDiffOn ℝ ∞ ZR O ∧ ContDiffOn ℝ ∞ ZI O ∧
      (∀ r ≤ j + 1, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (fun w : X => U w.1 w.2) z‖ ≤ tau * Kc * Profile) ∧
      (∀ r, r + p ≤ n → ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (fun w : X => ((tau : ℂ) / Complex.I)⁻¹ • U w.1 w.2 +
          incrementsModeComplexReducedOperator (F w.1) (hF w.1) (c w.1) (U w.1) w.2 - k w) z‖ ≤
        (2 * 2 ^ n * Mg) ^ p * (tau / ell) ^ p * Kc) ∧
      (∀ r ≤ j, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r ZR z‖ ≤
        CR * ‖incrementsModeRealPart (m := m)‖ * Kc * Profile + CH * KhR) ∧
      (∀ r ≤ j, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r ZI z‖ ≤
        CR * ‖incrementsModeImagPart (m := m)‖ * Kc * Profile + CH * KhI) := by
  dsimp only
  let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mg * Mg *
      ‖incrementsModeTransverseSourceCLM (m := m)‖
  let Kc := ‖incrementsModeComplexInclude (m := m)‖ * Ck * (KhR + KhI)
  let Cn := 2 * 2 ^ n * Mg
  let Profile := ∑ a ∈ Finset.range p, Cn ^ a
  let CR := 2 ^ j * Mg + 2 * 2 ^ (j + j) * Mg * max Mg ‖incrementsModeTransverseJet (m := m)‖
  let CH := (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖) / 2
  let k := fun z : X => incrementsModeComplexInclude
    (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
    Complex.I • incrementsModeComplexInclude
    (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2)
  let U := fun a => incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (F a) (hF a) (c a))
    (incrementsModeComplexFirstOrderB (F a) (hF a) (c a)) ((tau : ℂ) / Complex.I) p
    (fun x => k (a, x))
  let Ujoint := fun z : X => U z.1 z.2
  have hKc : 0 ≤ Kc := by dsimp [Kc, Ck]; positivity
  have hCn : 0 ≤ Cn := by dsimp [Cn]; positivity
  have hProfile : 0 ≤ Profile := Finset.sum_nonneg fun _ _ => pow_nonneg hCn _
  have hCR : 0 ≤ CR := by dsimp [CR]; positivity
  obtain ⟨hk, hkb⟩ := actual_joint_zeroFree_complex_source_slow_jets F hF c hR hI n O S hO hSO
    hBR hJ hhR hhI ell Mg Mg KhR KhI hell.le hMg hMg hKhR hKhI hBRb hJb hhRb hhIb
  obtain ⟨_hcompat, hU, hUraw⟩ := incrementsModeJointFiniteU_compatible_contDiffOn_scaled_jet
    F hF c k n p O S hO hSO hA hB hk tau ell Mg Kc htau hell hell1 hMg hKc hAb hBb hkb
  have hratio : Cn * tau / ell ≤ Cn :=
    (div_le_iff₀ hell).2 (mul_le_mul_of_nonneg_left htaul hCn)
  have hsum : (∑ a ∈ Finset.range p, (Cn * tau / ell) ^ a) ≤ Profile :=
    Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (by positivity) hratio a
  have hUb : ∀ r ≤ j + 1, ∀ z ∈ S,
      ell ^ r * ‖iteratedFDeriv ℝ r Ujoint z‖ ≤ tau * Kc * Profile := by
    intro r hr z hz
    exact (hUraw r (by omega) z hz).trans
      (mul_le_mul_of_nonneg_left hsum (mul_nonneg htau.le hKc))
  have hZ (L : Cdata →L[ℝ] D) (H0 : X → Source) (hH0 : ContDiffOn ℝ ∞ H0 O)
      (KH : ℝ) (hKH : 0 ≤ KH)
      (hHb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i H0 z‖ ≤ KH) :
      let Z := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
        (L ∘ U z.1) (fun x => H0 (z.1, x)) (fun _ => 0) z.2
      ContDiffOn ℝ ∞ Z O ∧
        ∀ r ≤ j, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r Z z‖ ≤
          CR * ‖L‖ * Kc * Profile + CH * KH := by
    dsimp only
    let Ku := ‖L‖ * tau * Kc * Profile
    have hKu : 0 ≤ Ku := by dsimp [Ku]; positivity
    have hv := L.contDiff.comp_contDiffOn hU
    have hvb : ∀ i ≤ j + 1, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i (L ∘ Ujoint) z‖ ≤ Ku := by
      intro i hi z hz
      exact (slow_linear_jet_bound L O hO Ujoint hU i ell
        (tau * Kc * Profile) hell.le z (hSO hz) (hUb i hi z hz)).trans_eq (by dsimp [Ku]; ring)
    obtain ⟨hs, hb⟩ := actual_joint_zeroFree_full_reconstruction_slow_jets F hF c
      (L ∘ Ujoint) H0 j O S hO hSO hG hJ hT hv hH0 ell Mg Ku KH hell hell1
      hMg hKu hKH hGb (fun i hi z hz => hJb i (by omega) z hz) hTb hvb hHb
    refine ⟨hs, ?_⟩
    intro r hr z hz
    have hb0 := hb r hr z hz
    change ell ^ (r + 1) * ‖iteratedFDeriv ℝ r
      (fun w : X => incrementsModeFullReconstruction (F w.1) (hF w.1) (c w.1)
        (L ∘ U w.1) (fun x => H0 (w.1, x)) (fun _ => 0) w.2) z‖ ≤
      CR * Ku + ell * (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖ * KH) / 2 at hb0
    have hscale : CR * Ku + ell * (2 ^ j * Mg * ‖incrementsModeTransverseSourceCLM (m := m)‖ * KH) / 2 ≤
        ell * (CR * ‖L‖ * Kc * Profile + CH * KH) := by
      calc
        _ = (CR * ‖L‖ * Kc * Profile) * tau + ell * (CH * KH) := by dsimp [Ku, CH]; ring
        _ ≤ (CR * ‖L‖ * Kc * Profile) * ell + ell * (CH * KH) :=
          add_le_add (mul_le_mul_of_nonneg_left htaul (by positivity)) (le_refl _)
        _ = _ := by ring
    have he : ell ^ (r + 1) * ‖iteratedFDeriv ℝ r
        (fun w : X => incrementsModeFullReconstruction (F w.1) (hF w.1) (c w.1)
          (L ∘ U w.1) (fun x => H0 (w.1, x)) (fun _ => 0) w.2) z‖ =
        ell * (ell ^ r * ‖iteratedFDeriv ℝ r
        (fun w : X => incrementsModeFullReconstruction (F w.1) (hF w.1) (c w.1)
          (L ∘ U w.1) (fun x => H0 (w.1, x)) (fun _ => 0) w.2) z‖) := by rw [pow_succ]; ring
    rw [he] at hb0
    exact (mul_le_mul_iff_right₀ hell).mp (hb0.trans hscale)
  obtain ⟨hZR, hZRb⟩ := hZ incrementsModeRealPart hR hhR KhR hKhR
    (fun i hi z hz => hhRb i (by omega) z hz)
  obtain ⟨hZI, hZIb⟩ := hZ incrementsModeImagPart hI hhI KhI hKhI
    (fun i hi z hz => hhIb i (by omega) z hz)
  refine ⟨hU, hZR, hZI, hUb, ?_, hZRb, hZIb⟩
  exact actual_joint_finite_residual_scaled_jets F hF c k n p O S hO hSO
    hA hB hk tau ell Mg Kc htau hell hell1 hMg hKc hAb hBb hkb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_secondary_mode_bounds
