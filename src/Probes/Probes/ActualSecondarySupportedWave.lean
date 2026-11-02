import Probes.ActualSecondaryFamily
import Probes.ActualJointChartTransfer

/-!
# Actual supported secondary waves and observation-chart jets

The two original reconstructed channels are extended by zero through the
actual partial joint chart and modulated by the original physical phase.
On that chart this is exactly the same local sine/cosine displacement. The
observation estimate differentiates its genuine pullback, including all
parameter derivatives of the real chart transition; no formal coordinate
representative replaces the actual map.
-/

noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
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

def actualSecondarySupportedWave
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (a : OpenPartialHomeomorph (Ep × M) X) (psi : Ep × M → ℝ)
    (tau : ℝ) (length : ℕ) : Ep × M → V :=
  let ZR := actualSecondaryRealChannel F hF c hR hI tau length
  let ZI := actualSecondaryImagChannel F hF c hR hI tau length
  fun y => Real.cos (psi y / tau) • (if y ∈ a.source then ZR (a y) else 0) -
    Real.sin (psi y / tau) • (if y ∈ a.source then ZI (a y) else 0)

theorem actualSecondarySupportedWave_eq_local
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (a : OpenPartialHomeomorph (Ep × M) X) (psi : Ep × M → ℝ) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) (y : Ep × M) (hy : y ∈ a.source)
    (hphase : psi y = phase (a y)) :
    actualSecondarySupportedWave F hF c hR hI a psi tau length y =
      actualSecondaryWave F hF c hR hI phase tau length (a y) := by
  simp only [actualSecondarySupportedWave, if_pos hy, hphase,
    actualSecondaryWave, actualSecondaryModulation]

/-- Genuine global smoothness and relative support, derived from the forcing
supports and original supported channel construction. -/
theorem actual_secondary_supported_wave_regular
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (length : ℕ) (tau : ℝ)
    (a : OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (hW : IsOpen W) (hsourceW : a.source ⊆ W)
    (K : Set (Ep × M)) (hK : IsClosed (Subtype.val ⁻¹' K : Set W))
    (hKsource : K ⊆ a.source)
    (hchart : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, X) ∞ a a.source)
    (hinverse : ∀ z ∈ a.target, a.symm z = (z.1, c z.1 z.2))
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) a.target)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) a.target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) a.target)
    (hT0 : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) a.target)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hhR : ContDiffOn ℝ ∞ hR a.target) (hhI : ContDiffOn ℝ ∞ hI a.target)
    (hinput : ∀ z ∈ a.target, z ∈ tsupport hR ∪ tsupport hI → a.symm z ∈ K)
    (psi : Ep × M → ℝ)
    (hpsi : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ psi W) :
    ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞
      (actualSecondarySupportedWave F hF c hR hI a psi tau length) W ∧
      tsupport (fun y : W => actualSecondarySupportedWave F hF c hR hI a psi tau length y) ⊆
        Subtype.val ⁻¹' K := by
  obtain ⟨hRext, hIext, hRsup, hIsup, _hsource, _htarget⟩ :=
    actual_secondary_supported_chart_pullback F hF c hR hI length tau a W hW hsourceW K hK hKsource
      hchart hinverse hBR hG hJ hT0 hA hB hhR hhI hinput
  let extR : Ep × M → V := fun y => if y ∈ a.source then
    actualSecondaryRealChannel F hF c hR hI tau length (a y) else 0
  let extI : Ep × M → V := fun y => if y ∈ a.source then
    actualSecondaryImagChannel F hF c hR hI tau length (a y) else 0
  have hr : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ extR W := hRext
  have hi : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ extI W := hIext
  have htheta : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (fun y => psi y / tau) W := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hpsi.mul (contMDiffOn_const (c := tau⁻¹))
  have hc := Real.contDiff_cos.contMDiff.comp_contMDiffOn htheta
  have hs := Real.contDiff_sin.contMDiff.comp_contMDiffOn htheta
  refine ⟨(hc.smul hr).sub (hs.smul hi), ?_⟩
  apply closure_minimal _ hK
  intro y hy
  by_contra hn
  have hzr : extR y = 0 := by
    have hnR : y ∉ tsupport (fun w : W => extR w) := fun h => hn (hRsup h)
    have hz := image_eq_zero_of_notMem_tsupport hnR
    exact hz
  have hzi : extI y = 0 := by
    have hnI : y ∉ tsupport (fun w : W => extI w) := fun h => hn (hIsup h)
    have hz := image_eq_zero_of_notMem_tsupport hnI
    exact hz
  apply hy
  change Real.cos (psi y / tau) • extR y - Real.sin (psi y / tau) • extI y = 0
  rw [hzr, hzi, smul_zero, smul_zero, sub_zero]

/-- The observation representative is genuinely smooth on its actual active
domain, by equality with the literal local wave and true chart composition. -/
theorem actual_secondary_supported_observation_contDiffOn
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (a : OpenPartialHomeomorph (Ep × M) X) (psi : Ep × M → ℝ) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) (kappa : Y → Ep × M) (O : Set Y)
    (hsource : ∀ y ∈ O, kappa y ∈ a.source)
    (hphase : ∀ y ∈ O, psi (kappa y) = phase (a (kappa y)))
    (htransition : ContDiffOn ℝ ∞ (a ∘ kappa) O)
    (hlocal : ContDiffOn ℝ ∞ (actualSecondaryWave F hF c hR hI phase tau length) a.target) :
    ContDiffOn ℝ ∞
      (actualSecondarySupportedWave F hF c hR hI a psi tau length ∘ kappa) O := by
  apply (hlocal.comp htransition (fun y hy => a.map_source (hsource y hy))).congr
  intro y hy
  exact actualSecondarySupportedWave_eq_local F hF c hR hI a psi phase tau length
    (kappa y) (hsource y hy) (hphase y hy)

/-- True joint observation-coordinate jets of the SAME supported wave. The
transition is literally `a ∘ kappa`; all of its mixed parameter jets enter.
Only the already produced local wave jets are consumed. -/
theorem actual_secondary_supported_observation_weighted_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (a : OpenPartialHomeomorph (Ep × M) X) (psi : Ep × M → ℝ) (phase : X → ℝ)
    (tau ell : ℝ) (length : ℕ) (kappa : Y → Ep × M)
    (O : Set Y) (hO : IsOpen O)
    (hsource : ∀ y ∈ O, kappa y ∈ a.source)
    (hphase : ∀ y ∈ O, psi (kappa y) = phase (a (kappa y)))
    (htransition : ContDiffOn ℝ ∞ (a ∘ kappa) O)
    (hlocal : ContDiffOn ℝ ∞ (actualSecondaryWave F hF c hR hI phase tau length) a.target)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) (K : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (y : Y) (hy : y ∈ O)
    (hlocalb : ∀ i ≤ j, tau ^ i * ‖iteratedFDeriv ℝ i
      (actualSecondaryWave F hF c hR hI phase tau length) (a (kappa y))‖ ≤ K)
    (htransitionb : ∀ i, 1 ≤ i → i ≤ j →
      ell ^ (i - 1) * ‖iteratedFDeriv ℝ i (a ∘ kappa) y‖ ≤ T i) :
    tau ^ j * ‖iteratedFDeriv ℝ j
      (actualSecondarySupportedWave F hF c hR hI a psi tau length ∘ kappa) y‖ ≤
        actualFastChartTransferCost T j * K := by
  have he : (actualSecondarySupportedWave F hF c hR hI a psi tau length ∘ kappa) =ᶠ[𝓝 y]
      (actualSecondaryWave F hF c hR hI phase tau length ∘ (a ∘ kappa)) := by
    filter_upwards [hO.mem_nhds hy] with z hz
    exact actualSecondarySupportedWave_eq_local F hF c hR hI a psi phase tau length
      (kappa z) (hsource z hz) (hphase z hz)
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact actual_fast_joint_chart_transfer T hT j (a ∘ kappa)
    (actualSecondaryWave F hF c hR hI phase tau length) O a.target hO a.open_target
    htransition hlocal (fun z hz => a.map_source (hsource z hz)) y hy tau ell K
      htau htaul hlocalb htransitionb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualSecondarySupportedWave_eq_local
#print axioms GlobalEmbedding.Continuation.actual_secondary_supported_wave_regular
#print axioms GlobalEmbedding.Continuation.actual_secondary_supported_observation_contDiffOn
#print axioms GlobalEmbedding.Continuation.actual_secondary_supported_observation_weighted_jets
