import Probes.ActualSecondaryJointReconstruction
import GlobalEmbedding.Paper.IncrementsSecondaryMode

/-!
# Actual nonzero-forcing source with full parameter jets

This is the original zero-free secondary source, on the actual joint domain.
Its budget is derived from the true h, true B row, and true included J. The
source itself and its derivatives are not assumed bounded as a new input.
The fixed Pi/Euclidean conversion norms and both complex channels are retained.
-/

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
local notation "Cdata" => Fin (m + 1) → ℂ

theorem actual_joint_zeroFree_source_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (h : X → Source)
    (n : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hh : ContDiffOn ℝ ∞ h O)
    (ell MB MJ Kh : ℝ) (hell : 0 ≤ ell)
    (hMB : 0 ≤ MB) (hMJ : 0 ≤ MJ) (hKh : 0 ≤ Kh)
    (hBRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => fun a =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ MB)
    (hJb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ MJ)
    (hhb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i h z‖ ≤ Kh) :
    let source := fun z : X => incrementsModeSource (F z.1) (hF z.1) (c z.1)
      (fun x => h (z.1, x)) (fun _ => 0) z.2
    ContDiffOn ℝ ∞ source O ∧
      ∀ k ≤ n, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k source z‖ ≤
        (‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
          ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB * MJ *
          ‖incrementsModeTransverseSourceCLM (m := m)‖) * Kh := by
  dsimp only
  let P := incrementsModeForcingSourceProjection (m := m) ∘ h
  let B := fun z : X => fun a =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 a : V)
  let Q := fun z : X => (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2
    (incrementsModeTransverseSource (fun x => h (z.1, x)) z.2) : V)
  let L := incrementsModeForcingSourcePairing (m := m) (N := N)
  have hP : ContDiffOn ℝ ∞ P O :=
    incrementsModeForcingSourceProjection.contDiff.comp_contDiffOn hh
  obtain ⟨hQ, hQb⟩ := actual_joint_forcing_slow_jets F hF c h n O S hO hSO hJ hh
    ell MJ Kh hell hMJ hKh hJb hhb
  have he : (fun z : X => incrementsModeSource (F z.1) (hF z.1) (c z.1)
      (fun x => h (z.1, x)) (fun _ => 0) z.2) = fun z => P z - L (B z) (Q z) := by
    funext z
    exact incrementsModeSource_zeroFree_eq (F z.1) (hF z.1) (c z.1)
      (fun x => h (z.1, x)) z.2
  rw [he]
  have hL : ContDiffOn ℝ ∞ (fun z => L (B z) (Q z)) O :=
    (L.contDiff.comp_contDiffOn hBR).clm_apply hQ
  refine ⟨hP.sub hL, ?_⟩
  intro k hk z hz
  have hPb := slow_linear_jet_bound incrementsModeForcingSourceProjection
    O hO h hh k ell Kh hell z (hSO hz) (hhb k hk z hz)
  have hLb := slow_bilinear_jet_bound_norm L O hO B Q hBR hQ k ell MB
    (2 ^ n * MJ * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) hell z (hSO hz)
    (fun i hi => hBRb i (hi.trans hk) z hz)
    (fun i hi => hQb i (hi.trans hk) z hz)
  have hp := (hP.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hl := (hL.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [fun_iteratedFDeriv_sub_apply hp hl]
  calc
    _ ≤ ell ^ k * (‖iteratedFDeriv ℝ k P z‖ +
        ‖iteratedFDeriv ℝ k (fun w => L (B w) (Q w)) z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ = ell ^ k * ‖iteratedFDeriv ℝ k P z‖ +
        ell ^ k * ‖iteratedFDeriv ℝ k (fun w => L (B w) (Q w)) z‖ := by ring
    _ ≤ ‖incrementsModeForcingSourceProjection (m := m)‖ * Kh +
        2 ^ k * (‖L‖ * MB) *
          (2 ^ n * MJ * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) :=
      add_le_add hPb hLb
    _ ≤ ‖incrementsModeForcingSourceProjection (m := m)‖ * Kh +
        2 ^ n * (‖L‖ * MB) *
          (2 ^ n * MJ * ‖incrementsModeTransverseSourceCLM (m := m)‖ * Kh) := by
      gcongr
      norm_num
    _ = _ := by dsimp only [L]; rw [pow_add]; ring

/-- Both real forcing channels feed the original complex source. Its full
joint source budget follows from actual B/J/h data. -/
theorem actual_joint_zeroFree_complex_source_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (n : ℕ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (ell MB MJ KhR KhI : ℝ) (hell : 0 ≤ ell)
    (hMB : 0 ≤ MB) (hMJ : 0 ≤ MJ) (hKhR : 0 ≤ KhR) (hKhI : 0 ≤ KhI)
    (hBRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => fun a =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (c w.1) w.2 0 a : V)) z‖ ≤ MB)
    (hJb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ MJ)
    (hhRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hR z‖ ≤ KhR)
    (hhIb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hI z‖ ≤ KhI) :
    let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
      ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB * MJ *
        ‖incrementsModeTransverseSourceCLM (m := m)‖
    let source := fun z : X => incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
      Complex.I • incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2)
    ContDiffOn ℝ ∞ source O ∧
      ∀ k ≤ n, ∀ z ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k source z‖ ≤
        ‖incrementsModeComplexInclude (m := m)‖ * Ck * (KhR + KhI) := by
  dsimp only
  let kr := fun z : X => incrementsModeSource (F z.1) (hF z.1) (c z.1)
    (fun x => hR (z.1, x)) (fun _ => 0) z.2
  let ki := fun z : X => incrementsModeSource (F z.1) (hF z.1) (c z.1)
    (fun x => hI (z.1, x)) (fun _ => 0) z.2
  let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
    ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * MB * MJ *
      ‖incrementsModeTransverseSourceCLM (m := m)‖
  obtain ⟨hr, hrb⟩ := actual_joint_zeroFree_source_slow_jets F hF c hR n O S hO hSO
    hBR hJ hhR ell MB MJ KhR hell hMB hMJ hKhR hBRb hJb hhRb
  obtain ⟨hi, hib⟩ := actual_joint_zeroFree_source_slow_jets F hF c hI n O S hO hSO
    hBR hJ hhI ell MB MJ KhI hell hMB hMJ hKhI hBRb hJb hhIb
  have hcr := incrementsModeComplexInclude.contDiff.comp_contDiffOn hr
  have hci := incrementsModeComplexInclude.contDiff.comp_contDiffOn hi
  refine ⟨hcr.add (hci.const_smul Complex.I), ?_⟩
  intro k hk z hz
  have hrc := slow_linear_jet_bound incrementsModeComplexInclude O hO kr hr k ell
    (Ck * KhR) hell z (hSO hz) (hrb k hk z hz)
  have hic := slow_linear_jet_bound incrementsModeComplexInclude O hO ki hi k ell
    (Ck * KhI) hell z (hSO hz) (hib k hk z hz)
  have hdr := (hcr.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  have hdi := (hci.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (k : ℕ∞ω) ≤ ∞)
  simp only [Function.comp_def] at hdr hdi
  rw [fun_iteratedFDeriv_add_apply hdr (hdi.const_smul Complex.I),
    iteratedFDeriv_const_smul_apply' hdi]
  calc
    _ ≤ ell ^ k * (‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ kr) z‖ +
        ‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ ki) z‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Function.comp_def, kr, ki, norm_smul, Complex.norm_I, one_mul] using norm_add_le
        (iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ kr) z)
        (Complex.I • iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ ki) z)
    _ = ell ^ k * ‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ kr) z‖ +
        ell ^ k * ‖iteratedFDeriv ℝ k (incrementsModeComplexInclude ∘ ki) z‖ := by ring
    _ ≤ ‖incrementsModeComplexInclude (m := m)‖ * (Ck * KhR) +
        ‖incrementsModeComplexInclude (m := m)‖ * (Ck * KhI) := add_le_add hrc hic
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_zeroFree_source_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_joint_zeroFree_complex_source_slow_jets
