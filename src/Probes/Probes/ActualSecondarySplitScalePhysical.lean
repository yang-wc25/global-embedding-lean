import Probes.ActualSecondaryPhysicalFamily
import Probes.ActualIncrementSplitScaleJointFinite

/-!
# Actual secondary physical metric residual: all joint jets

The source estimate, finite polynomial, complete physical tensor identity and
native row operator are assembled here. No output residual estimate is an
input. The bound keeps `(τ/ℓ)^length`, the actual original 11 row factor two,
the same real/imaginary forcing, and the same varying chosen chart throughout.
-/

noncomputable section
open Manifold Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

theorem actual_secondary_physical_error_split_scale_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ p, chart p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hOt : ∀ z ∈ O, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((chart z.1).symm z.2)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ)
      (β.comp β.adjoint).IsInvertible)
    (hR hI : X → Source) (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (hRsymm : ∀ z ∈ O, ∀ i j, hR z i j = hR z j i)
    (hIsymm : ∀ z ∈ O, ∀ i j, hI z i j = hI z j i)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1).symm z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) ((chart z.1).symm z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (chart z.1).symm z.2)) O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (chart z.1).symm z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (chart z.1).symm z.2) O)
    (n length : ℕ) (tau ell Mg KhR KhI : ℝ)
    (htau : 0 < tau) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKhR : 0 ≤ KhR) (hKhI : 0 ≤ KhI)
    (hBRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => fun a =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (chart w.1).symm w.2 0 a : V)) z‖ ≤ Mg)
    (hJb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => (normalSpace (I := 𝓙) (F w.1) ((chart w.1).symm w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (chart w.1).symm w.2)) z‖ ≤ Mg)
    (hAb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (chart w.1).symm w.2) z‖ ≤ Mg)
    (hBb : ∀ i ≤ n, ∀ z ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (chart w.1).symm w.2) z‖ ≤ Mg)
    (hhRb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hR z‖ ≤ KhR)
    (hhIb : ∀ i ≤ n, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i hI z‖ ≤ KhI) :
    let Ck := ‖incrementsModeForcingSourceProjection (m := m)‖ + 2 ^ (n + n) *
      ‖incrementsModeForcingSourcePairing (m := m) (N := N)‖ * Mg * Mg *
        ‖incrementsModeTransverseSourceCLM (m := m)‖
    let Ksource := ‖incrementsModeComplexInclude (m := m)‖ * Ck * (KhR + KhI)
    let Kerr := (2 * 2 ^ n * Mg) ^ length * (tau / ell) ^ length * Ksource
    ContDiffOn ℝ ∞ (actualSecondaryPhysicalError F hF chart hR hI tau length) O ∧
      ∀ j, j + length ≤ n → ∀ z ∈ S, ell ^ j * ‖iteratedFDeriv ℝ j
        (actualSecondaryPhysicalError F hF chart hR hI tau length) z‖ ≤ 2 * Kerr := by
  intro Ck Ksource Kerr
  let c : Ep → D → M := fun p => (chart p).symm
  let source := actualSecondaryComplexSource F hF c hR hI
  let U := actualSecondarySolution F hF c hR hI tau length
  let residual := actualSecondaryReducedResidual F hF c hR hI tau length
  obtain ⟨hs, hsb⟩ := actual_joint_zeroFree_complex_source_slow_jets F hF c hR hI n O S hO hSO
    hBR hJ hhR hhI ell Mg Mg KhR KhI hell.le hMg hMg hKhR hKhI hBRb hJb hhRb hhIb
  have hsource : 0 ≤ Ksource := by dsimp [Ksource, Ck]; positivity
  have hKerr : 0 ≤ Kerr := by dsimp [Kerr]; positivity
  have hU : ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) O :=
    actualSecondarySolution_contDiffOn F hF c hR hI tau length O hO hA hB hs
  have hres : ContDiffOn ℝ ∞ residual O :=
    actual_joint_reduced_residual_contDiffOn F hF c (fun z => U z.1 z.2) source O hO hA hB hU hs
      ((tau : ℂ) / Complex.I)
  have hresb := actual_increment_joint_residual_split_scale_jets F hF c source n length O S hO hSO hA hB hs
    tau ell Mg Ksource htau hell hell1 hMg hsource hAb hBb hsb
  have he := actual_secondary_physical_error_eq_reduced F hF chart hchart O hO hOt hinj hfree
    hR hI hhR hhI hRsymm hIsymm tau htau length
  have hrows : ContDiffOn ℝ ∞ (fun z => actualModeResidualRows (residual z)) O :=
    actualModeResidualRows.contDiff.comp_contDiffOn hres
  refine ⟨hrows.congr he, ?_⟩
  intro j hj z hz
  have hg : actualSecondaryPhysicalError F hF chart hR hI tau length =ᶠ[𝓝 z]
      (fun w => actualModeResidualRows (residual w)) := by
    filter_upwards [hO.mem_nhds (hSO hz)] with w hw
    exact he hw
  rw [(hg.iteratedFDeriv ℝ j).eq_of_nhds]
  exact (slow_linear_jet_bound actualModeResidualRows O hO residual hres j ell Kerr hell.le
    z (hSO hz) (hresb j hj z hz)).trans
      (mul_le_mul_of_nonneg_right actualModeResidualRows_norm_le hKerr)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_physical_error_split_scale_jets
