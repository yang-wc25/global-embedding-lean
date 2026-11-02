import GlobalEmbedding.Paper.IncrementsModeJointSourceRegularity
import GlobalEmbedding.Paper.IncrementsModeComplexLinearity
import GlobalEmbedding.Paper.IncrementsSupportedAmplitudeSmoothGlue

/-!
# Actual normalized primary source: joint smoothness on the original open region

Source: original `lem:increments`, main.tex594–609,638–650.
DAG: `increments-normalized-primary-source-joint-smoothness`, exclusive W4.
STAGE2 ONLY: precise actual header/doc awaiting ROOT lock; one expected named hole.
No accepted provider, source, norm, amplitude or reconstruction is modified.
-/

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Paper

variable {m N : ℕ} {Ep T : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- The SAME original normalized primary ambient free normal and native complex
source are jointly smooth on the original open parameter/spatial region. Only
its full active combined-cutoff support needs positive argument and a genuine
primitive smooth domain; observation-set reserve alone is not enough.

Natural-language proof: write eta=cs*cp and nV for the original normal inclusion.
The literal ambient vf is sqrt2*tau times (eta*sqrt(L(A))) smul nV by native
fiber inclusion and scalar associativity. At each point of Omega in tsupport eta,
hactive places the point in the original open U and hpositive supplies strict
positivity. Apply the accepted public positive-reserve amplitude ContDiffAt
endpoint, with no new sqrt or product derivative proof. Off tsupport eta, the
accepted supported-amplitude eventually-zero endpoint gives a true zero germ
without any positivity or primitive smoothness hypothesis there. Native scalar
smoothness and locality give the actual ambient vf ContDiffOn conclusion.

For actual k, reuse W2's sole public source split. Its h=0 zero-free term vanishes
by the accepted source scalar-zero identity and native map_zero; thus the literal
source equals 2 times canonical Q(actual BRow)(ambient vf). At active points the
original U gives genuine BRow smoothness; native fixed CLM composition/application
and Include prove actual source smoothness. At inactive points the same amplitude
zero germ gives a source zero germ even if the primitive fields are irregular
there. Native locality yields actual complex k ContDiffOn Omega. No hJ, desired
source regularity, global inactive reserve, uniform norm bound or extra source
jet order is assumed. Tau is an arbitrary fixed external real scale; empty Omega,
empty active support, tau=0, m=0, N=0 and zero-dimensional parameters are allowed.
Source: original lem:increments, main.tex594–609 and638–650. -/
theorem increments_normalized_primary_source_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (chart : Ep → D → M)
    (normal : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (chart p x))
    (Omega U : Set X) (hOmega : IsOpen Omega) (hU : IsOpen U)
    (L : X → T →L[ℝ] ℝ) (A : X → T) (cp cs : X → ℝ)
    (hactive : Omega ∩ tsupport (fun z ↦ cs z * cp z) ⊆ U)
    (hL : ContDiffOn ℝ ∞ L U) (hA : ContDiffOn ℝ ∞ A U)
    (hcp : ContDiffOn ℝ ∞ cp U) (hcs : ContDiffOn ℝ ∞ cs U)
    (hn : ContDiffOn ℝ ∞ (fun z : X ↦ (normal z.1 z.2 : V)) U)
    (hB : ContDiffOn ℝ ∞ (fun z : X ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) U)
    (hpositive : ∀ z ∈ Omega ∩ tsupport (fun y ↦ cs y * cp y), 0 < L z (A z))
    (tau : ℝ) :
    let vf := fun (p : Ep) (x : D) ↦
      cs (p, x) • ((Real.sqrt 2 * 1 * tau * (cp (p, x) *
        Real.sqrt (L (p, x) (A (p, x))))) • normal p x)
    let k := fun z : X ↦ incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (chart z.1)
        (fun _ _ _ ↦ 0) (vf z.1) z.2)
    ContDiffOn ℝ ∞ (fun z : X ↦ (vf z.1 z.2 : V)) Omega ∧
      ContDiffOn ℝ ∞ k Omega := by
  intro vf k
  let eta : X → ℝ := fun z ↦ cs z * cp z
  let nV : X → V := fun z ↦ (normal z.1 z.2 : V)
  let amp : X → V := fun z ↦ (eta z * Real.sqrt (L z (A z))) • nV z
  let v : X → V := fun z ↦ (vf z.1 z.2 : V)
  let Q := incrementsModeForcingSourcePairing (m := m) (N := N)
  let J := incrementsModeComplexInclude (m := m)
  let Brow := fun z : X ↦ fun i : Fin (m + 1) ↦
    (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)
  have hv_eq : v = (fun z ↦ (Real.sqrt 2 * tau) • amp z) := by
    funext z
    dsimp [v, vf, amp, eta, nV]
    simp only [smul_smul]
    congr 1
    ring
  have hamp_zero {z : X} (hz : z ∉ tsupport eta) :
      amp =ᶠ[𝓝 z] (fun _ ↦ (0 : V)) :=
    increments_supported_amplitude_eventually_zero L A eta nV hz
  have hv_zero {z : X} (hz : z ∉ tsupport eta) :
      v =ᶠ[𝓝 z] (fun _ ↦ (0 : V)) := by
    filter_upwards [hamp_zero hz] with y hy
    rw [hv_eq]
    change (Real.sqrt 2 * tau) • amp y = 0
    rw [hy, smul_zero]
  have hv_at (z : X) (hz : z ∈ Omega) : ContDiffAt ℝ ∞ v z := by
    rw [hv_eq]
    by_cases ht : z ∈ tsupport eta
    · exact (increments_positive_reserve_amplitude_contDiffAt U hU L A eta nV
        hL hA (hcs.mul hcp) hn (hactive ⟨hz, ht⟩)
        (hpositive z ⟨hz, ht⟩)).const_smul (Real.sqrt 2 * tau)
    · exact (contDiffAt_const.congr_of_eventuallyEq (hamp_zero ht)).const_smul
        (Real.sqrt 2 * tau)
  have hk_eq (z : X) : k z = (2 : ℝ) • J (Q (Brow z) (v z)) := by
    have hzero : incrementsModeSource (F z.1) (hF z.1) (chart z.1)
        (fun _ _ _ ↦ 0) (fun _ ↦ 0) z.2 = 0 := by
      simpa only [zero_smul] using incrementsModeSource_zero_smul
        (F z.1) (hF z.1) (chart z.1) (fun _ ↦ 0) z.2 0
    dsimp only [k]
    rw [incrementsModeSource_eq_zeroFree_add, hzero, zero_add, map_smul]
  refine ⟨hOmega.contDiffOn_iff.mpr (fun z hz ↦ hv_at z hz),
    hOmega.contDiffOn_iff.mpr ?_⟩
  intro z hz
  by_cases ht : z ∈ tsupport eta
  · have hb : ContDiffAt ℝ ∞ Brow z := hB.contDiffAt (hU.mem_nhds (hactive ⟨hz, ht⟩))
    have hq := Q.contDiff.contDiffAt.comp z hb
    have hr := hq.clm_apply (hv_at z hz)
    have hk := (J.contDiff.contDiffAt.comp z hr).const_smul (2 : ℝ)
    exact hk.congr_of_eventuallyEq (Eventually.of_forall hk_eq)
  · have hk_zero : k =ᶠ[𝓝 z] (fun _ ↦ (0 : Fin (m + 1) → ℂ)) := by
      filter_upwards [hv_zero ht] with y hy
      rw [hk_eq, hy]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hk_zero

end GlobalEmbedding.Paper
