import Probes.ActualSecondarySupportedWave

/-! Actual supported waves need phase smoothness only on their actual chart
source. Off that source, the closed genuine forcing support supplies a zero
germ. No extension of a locally defined original phase is assumed smooth. -/

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

theorem actual_secondary_supported_wave_local_phase_regular
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
    (hpsi : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ psi a.source) :
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
  have htheta : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (fun y => psi y / tau) a.source := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hpsi.mul (contMDiffOn_const (c := tau⁻¹))
  have hc := Real.contDiff_cos.contMDiff.comp_contMDiffOn htheta
  have hs := Real.contDiff_sin.contMDiff.comp_contMDiffOn htheta
  have hlocal : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞
      (actualSecondarySupportedWave F hF c hR hI a psi tau length) a.source :=
    (hc.smul (hr.mono hsourceW)).sub (hs.smul (hi.mono hsourceW))
  have hzero : ∀ y ∈ W, y ∉ K → actualSecondarySupportedWave F hF c hR hI a psi tau length y = 0 := by
    intro y hy hn
    have hzr : extR y = 0 := by
      have hz : (⟨y,hy⟩ : W) ∉ tsupport (fun w : W => extR w) := fun h => hn (hRsup h)
      have hz0 := image_eq_zero_of_notMem_tsupport hz
      exact hz0
    have hzi : extI y = 0 := by
      have hz : (⟨y,hy⟩ : W) ∉ tsupport (fun w : W => extI w) := fun h => hn (hIsup h)
      have hz0 := image_eq_zero_of_notMem_tsupport hz
      exact hz0
    change Real.cos (psi y/tau) • extR y - Real.sin (psi y/tau) • extI y = 0
    rw [hzr,hzi,smul_zero,smul_zero,sub_zero]
  have hopen : IsOpen (Subtype.val '' (Subtype.val ⁻¹' K : Set W)ᶜ) :=
    hW.isOpenMap_subtype_val _ hK.isOpen_compl
  refine ⟨?_, ?_⟩
  · intro y hy
    by_cases hys : y ∈ a.source
    · exact (hlocal.contMDiffAt (a.open_source.mem_nhds hys)).contMDiffWithinAt
    · have hyn : y ∉ K := fun h => hys (hKsource h)
      have hym : y ∈ Subtype.val '' (Subtype.val ⁻¹' K : Set W)ᶜ := ⟨⟨y,hy⟩,hyn,rfl⟩
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hym] with x hx
      rcases hx with ⟨w,hw,rfl⟩
      exact hzero w w.property hw
  · apply closure_minimal _ hK
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

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_supported_wave_local_phase_regular
