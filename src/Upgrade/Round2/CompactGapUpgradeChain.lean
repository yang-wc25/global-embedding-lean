import Round2.RankQGapGlobalAvoidance
import Round2.CompactGapUpgradeAfterRank
import Upgrade.IncidenceOriginalDiagonal
import Upgrade.CompactAtlasSupport
import Upgrade.SupportedEmptySource

/-!
# The full DQ-free geometric upgrade chain, conditional on exact probes and normal gap

The single rank-q operation is enough: the actual normal dimension is q+1,
and the original phase condition gives rank at least q. After recomputing
and protecting the current low-rank locus, its compact complement is actual
full rank. The dimension-dependent supported operation and the final value
operation are then called on new current maps and newly prepared actual
finite wave lists. The same original atlas and diagonal neighborhood are
used throughout, and the literal original C² budgets telescope.

This theorem deliberately takes `GapControlledUpgradeProbeProvider`, whose
construction is owned by the upstream probes/normal-identification work.
Its normal-control part now consists only of the zeroth-order gap. The actual
Schur and n=3 source derivatives are controlled by the proved cancellation at
incidence zeros; no spatial DQ bound is required. The original finite geometry,
recomputed current bad sets, protected closures and all C² budgets are retained.
It is a conditional closure of the geometric chain, not the original
unconditional target and not an acceptance-counter update.
-/

noncomputable section
open Set Bundle Manifold Module Topology GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [CompactSpace M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Conditional geometric upgrade with an interior support cover. No
connectedness, orientation, nonempty source, incidence-rank, no-new-bad-point,
or final-embedding premise occurs. -/
theorem exists_sameMetric_phase_embedding_of_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (provider : GapControlledUpgradeProbeProvider (N := N) A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      probeAtlasCj A 2 (G - F) ≠ ⊤ ∧ (probeAtlasCj A 2 (G - F)).toReal < epsilon := by
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨delta, hdelta, D, hD, hdiag, hsym, hP, hdistinct, hdiagonal⟩ :=
    exists_originalC2_uniform_diagonal_separation A hA hcoverA F hF himm
  obtain ⟨ephase, lam, margin, hephase, _, _, hprotectPhase⟩ :=
    exists_originalC2_phase_protection A hA hcompact hsupportCover (by omega : 2 ≤ n)
      F hF himm hphase
  let b := min epsilon (min ephase delta) / 4
  have hb : 0 < b := div_pos (lt_min hepsilon (lt_min hephase hdelta)) (by norm_num)
  have htwoE : 2 * b < epsilon := by
    have h := min_le_left epsilon (min ephase delta)
    dsimp only [b]
    linarith
  have htwoP : 2 * b ≤ ephase := by
    have h : min epsilon (min ephase delta) ≤ ephase :=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp only [b]
    linarith
  have htwoD : 2 * b ≤ delta := by
    have h : min epsilon (min ephase delta) ≤ delta :=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp only [b]
    linarith
  obtain ⟨r, waves, hremove⟩ := exists_rankQCoincidence_removal_from_gap_probes
    A hA hcompact hcoverA F hF himm hphase hn hN hP hdistinct
  obtain ⟨probe, ⟨control⟩⟩ := provider F hF himm hphase r waves
  obtain ⟨t, ht, htt, u, hu, hsmall₁, hmetric₁, havoid₁⟩ := hremove probe control b hb
  let F₁ := probe.map t u
  have hF₁ := probe.slice_smooth t u
  have himm₁ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₁ x) :=
    fun x ↦ immersion_of_inducedMetric_eq F F₁ x (hmetric₁ x) (himm x)
  have hphase₁ : PhaseRegular F₁ hF₁ :=
    (hprotectPhase F₁ hF₁ (hsmall₁.trans (ENNReal.ofReal_le_ofReal (by linarith)))).1
  have hseparated₁ : ∀ x y, (x, y) ∈ Dᶜ →
      finrank ℝ (trueSecondForm F₁ hF₁ x).range ≤ n * (n - 1) / 2 → F₁ x ≠ F₁ y := by
    intro x y hz hr hcoin
    exact havoid₁ (x,y) hz ⟨hr, hcoin⟩
  have hsymP : ∀ x y, (x, y) ∈ Dᶜ → (y, x) ∈ Dᶜ := by
    intro x y hxy hyx
    exact hxy (hsym y x hyx)
  have hdiagonal₁ : ∀ (G : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ G →
      probeAtlasCj A 2 (G - F₁) ≤ ENNReal.ofReal b →
      ∀ x y, (x, y) ∈ D → G x = G y → x = y := by
    intro G hG hsmall
    apply hdiagonal G hG
    have htotal := probeAtlasC2_two_stage_budget A hA F F₁ G hF hF₁ hG
      hb.le hb.le hsmall₁ hsmall
    exact htotal.trans (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨G, hG, hsmallG, hmetricG, himmG, _, hembG⟩ :=
    exists_embedding_after_actual_rank_removal_of_gap_probes A hA hcompact hcoverA provider
      F₁ hF₁ himm₁ hphase₁ hn hN hP hdistinct hsymP hseparated₁ b hb hdiagonal₁ hb
  have htotal := probeAtlasC2_two_stage_budget A hA F F₁ G hF hF₁ hG
    hb.le hb.le hsmall₁ hsmallG
  have hfinite : probeAtlasCj A 2 (G - F) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top htotal
  have hreal : (probeAtlasCj A 2 (G - F)).toReal < epsilon := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ b + b)] at h
    exact h.trans_lt (by linarith)
  exact ⟨G, hG, fun x ↦ (hmetricG x).trans (hmetric₁ x), himmG,
    (hprotectPhase G hG (htotal.trans (ENNReal.ofReal_le_ofReal (by linarith)))).1,
    hembG, hfinite, hreal⟩

/-- The raw original atlas need not have supports whose interiors cover.
Compact support enlargement is actually constructed, probes are called on
that selected atlas, and the proved norm monotonicity returns the strict
bound in the original atlas norm. The sole remaining provider hypothesis
is explicit and remains upstream. -/
theorem exists_originalAtlas_sameMetric_phase_embedding_of_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (provider : ∀ (A' : BufferedAtlas M E), IsSmoothBufferedAtlas A' →
      (∀ i, IsCompact (A'.support i)) → (∀ x, ∃ i, x ∈ interior (A'.support i)) →
      GapControlledUpgradeProbeProvider (N := N) A')
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      probeAtlasCj A 2 (G - F) ≠ ⊤ ∧ (probeAtlasCj A 2 (G - F)).toReal < epsilon := by
  classical
  by_cases hempty : IsEmpty M
  · letI := hempty
    exact exists_sameMetric_phase_embedding_of_empty_source A hA F hF hphase hepsilon
  ·
    obtain ⟨S, hAS, hScompact, hSsource, hScover, hA', hnorm⟩ :=
      exists_compact_enlarged_support_cover (N := N) A hA hcompact
    let A' := enlargeBufferedAtlasSupport A S
    obtain ⟨G, hG, hmetric, himmG, hphaseG, hembG, hfinite, hreal⟩ :=
      exists_sameMetric_phase_embedding_of_gap_probes A' hA' hScompact hScover
        (provider A' hA' hScompact hScover) F hF himm hphase hn hN hepsilon
    have hle := hnorm 2 (G - F)
    exact ⟨G, hG, hmetric, himmG, hphaseG, hembG,
      ne_top_of_le_ne_top hfinite hle, (ENNReal.toReal_mono hfinite hle).trans_lt hreal⟩

end GlobalEmbedding.Upgrade
