import Round2.CompactGapSupportedStage
import Round2.CompactGapUpgradeFinish
import Upgrade.ProtectionTrueRank

/-!
# Actual gap-only compact assembly after rank-coincidence removal

The current map's own low-rank locus is recomputed, protected with a closed
neighborhood margin, and given a full-rank compact complement and buffer.
The actual second operation is then performed using new current-map probes.
Its supported locus is recomputed again; partners in the first protected
neighborhood are covered by the retained two-endpoint value gap. Finally the
remaining compact pair region supplies its actual nonsupported value waves.
All operations use the same original atlas and diagonal neighborhood.

The proof reuses the prior actual compact protection and budget argument,
calling the newly verified gap-only supported stage and final value stage.
No required rank, protected-region existence, or global avoidance result has
been added to the provider.
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

theorem exists_embedding_after_actual_rank_removal_of_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (provider : GapControlledUpgradeProbeProvider (N := N) A)
    (F₁ : M → V) (hF₁ : ContMDiff IM 𝓘(ℝ, V) ∞ F₁)
    (himm₁ : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₁ x))
    (hphase₁ : PhaseRegular F₁ hF₁) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {D : Set (M × M)} (hP : IsCompact Dᶜ) (hdistinct : ∀ z ∈ Dᶜ, z.1 ≠ z.2)
    (hsym : ∀ x y, (x, y) ∈ Dᶜ → (y, x) ∈ Dᶜ)
    (hseparated : ∀ x y, (x, y) ∈ Dᶜ →
      finrank ℝ (trueSecondForm F₁ hF₁ x).range ≤ n * (n - 1) / 2 → F₁ x ≠ F₁ y)
    (delta : ℝ) (hdelta : 0 < delta)
    (hdiagonal : ∀ (G : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ G →
      probeAtlasCj A 2 (G - F₁) ≤ ENNReal.ofReal delta →
      ∀ x y, (x, y) ∈ D → G x = G y → x = y)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      probeAtlasCj A 2 (G - F₁) ≤ ENNReal.ofReal epsilon ∧
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F₁ x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G := by
  classical
  obtain ⟨O, W, hO, hW, hbadO, hC, hCW, hWcompact, hWrank, d, hd, hgapO⟩ :=
    exists_current_trueRank_protected_complement F₁ hF₁ himm₁ (n * (n - 1) / 2)
      hP hsym hseparated
  let C : Set M := Oᶜ
  have hfull₁ : ∀ x ∈ C, Function.Surjective (trueSecondForm F₁ hF₁ x) := by
    intro x hx
    exact actual_fullRank_of_rank_gt_q F₁ hF₁ x (himm₁ x) (by omega : 1 ≤ n) hN
      (hWrank x (subset_closure (hCW hx)))
  have hsupportCover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨egap, hegap, hprotectO⟩ :=
    exists_probeAtlasC2_protected_gap_budget A hA hsupportCover hd hgapO
  let b := min epsilon delta / 4
  have hb : 0 < b := div_pos (lt_min hepsilon hdelta) (by norm_num)
  have htwoE : 2 * b ≤ epsilon := by
    have he := min_le_left epsilon delta
    dsimp only [b]
    linarith
  have htwoD : 2 * b ≤ delta := by
    have he := min_le_right epsilon delta
    dsimp only [b]
    linarith
  let PC : Set (M × M) := Dᶜ ∩ (C ×ˢ C)
  have hPC : IsCompact PC := hP.inter_right (hO.isClosed_compl.prod hO.isClosed_compl)
  obtain ⟨F₂, hF₂, hsmall₂, hmetric₂, himm₂, hphase₂, hfull₂, hsep₂, _⟩ :=
    exists_actual_supported_stage_of_gap_probes A hA hcompact hcoverA provider F₁ hF₁ himm₁ hphase₁ hn hN
      hC hfull₁ hPC (fun z hz ↦ hdistinct z hz.1) (fun _ hz ↦ hz.2.1)
      (lt_min hb hegap)
  have hsmall₂b : probeAtlasCj A 2 (F₂ - F₁) ≤ ENNReal.ofReal b :=
    hsmall₂.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hgapO₂ := hprotectO F₂ (hsmall₂.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  have hseparated₂ : ∀ z ∈ Dᶜ, z.1 ∈ C →
      HasSupportedKernel (trueSecondForm F₂ hF₂ z.1) → F₂ z.1 ≠ F₂ z.2 := by
    intro z hz hx hs hcoin
    by_cases hy : z.2 ∈ C
    · exact hsep₂ z ⟨hz, hx, hy⟩ hs hcoin
    · have hyO : z.2 ∈ O := not_not.mp hy
      have hg := hgapO₂ z hz (Or.inr (subset_closure hyO))
      rw [hcoin, sub_self, norm_zero] at hg
      linarith
  obtain ⟨S, WS, hS, hWS, hsupportedS, hCS, hCSW, hWScompact, hWSgood, e, he, hgapS⟩ :=
    exists_current_supported_protected_complement F₂ hF₂ himm₂ hphase₂ hC hfull₂
      hP hsym hseparated₂
  have hremaining : ∀ z ∈ remainingPairRegion Dᶜ O S, F₂ z.1 = F₂ z.2 →
      Function.Surjective (trueSecondForm F₂ hF₂ z.1) ∧
        ¬ HasSupportedKernel (trueSecondForm F₂ hF₂ z.1) := by
    intro z hz _
    have hxC : z.1 ∈ C := fun hx ↦ hz.2.1 (Or.inl hx)
    have hxS : z.1 ∉ S := fun hx ↦ hz.2.1 (Or.inr hx)
    exact hWSgood z.1 (subset_closure (hCSW ⟨hxC, hxS⟩))
  have hgapO₂strict : ∀ z ∈ Dᶜ, z.1 ∈ closure O ∨ z.2 ∈ closure O →
      d / 4 < ‖F₂ z.1 - F₂ z.2‖ := by
    intro z hz ho
    have hg := hgapO₂ z hz ho
    linarith
  have hdiagonal₂ : ∀ (G : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ G →
      probeAtlasCj A 2 (G - F₂) ≤ ENNReal.ofReal b →
      ∀ x y, (x, y) ∈ D → G x = G y → x = y := by
    intro G hG hsmall
    apply hdiagonal G hG
    have htotal := probeAtlasC2_two_stage_budget A hA F₁ F₂ G hF₁ hF₂ hG
      hb.le hb.le hsmall₂b hsmall
    exact htotal.trans (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨G, hG, hsmallG, hmetricG, himmG, hphaseG, hembG⟩ :=
    exists_embedding_from_current_protected_regions_of_gap_probes A hA hcompact hcoverA provider
      F₂ hF₂ himm₂ hphase₂ hn hN hP hdistinct hO hS
      (by positivity : 0 < d / 4) he hgapO₂strict hgapS hremaining b hb hdiagonal₂ hb
  have htotal := probeAtlasC2_two_stage_budget A hA F₁ F₂ G hF₁ hF₂ hG
    hb.le hb.le hsmall₂b hsmallG
  exact ⟨G, hG, htotal.trans (ENNReal.ofReal_le_ofReal (by linarith)),
    fun x ↦ (hmetricG x).trans (hmetric₂ x), himmG, hphaseG, hembG⟩

end GlobalEmbedding.Upgrade
