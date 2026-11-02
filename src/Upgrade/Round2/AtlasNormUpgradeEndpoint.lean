import Round2.AtlasNormTransfer
import Round2.AtlasExistence
import Round2.CompactGapUpgradeChain

/-!
# A single fixed probes atlas suffices for every original C² tolerance

The actual geometric atlas-norm comparison supplies a positive constant
before any perturbed map is chosen.  Run the existing compact upgrade chain
with the original tolerance divided by that constant, then transfer the
finite strict C² estimate to the user's original atlas.

The native atlas is constructed once, before the probes provider, the
requested original atlas, the immersion and epsilon.  No probes provider on
the requested output atlas is assumed.  The full exact-probes and chosen
normal-gap provider on the one native atlas remains an explicit upstream
dependency; this is not an unconditional theorem or an acceptance update.
-/

noncomputable section
open Set Bundle Manifold Topology GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual provider is needed on one fixed atlas only.  Its same-metric
phase-regular embedding output satisfies a strict tolerance in any prescribed
original compact smooth atlas, with that exact original norm retained. -/
theorem exists_originalAtlas_sameMetric_phase_embedding_of_fixed_gap_probes
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hAc : ∀ i, IsCompact (A.support i))
    (hcoverA : ∀ x, ∃ i, x ∈ interior (A.support i))
    (provider : GapControlledUpgradeProbeProvider (N := N) A)
    (A₀ : BufferedAtlas M E) (hA₀ : IsSmoothBufferedAtlas A₀)
    (hA₀c : ∀ i, IsCompact (A₀.support i))
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      probeAtlasCj A₀ 2 (G - F) ≠ ⊤ ∧
      (probeAtlasCj A₀ 2 (G - F)).toReal < epsilon := by
  have hcover : ∀ x, ∃ i, x ∈ A.support i := fun x ↦ by
    obtain ⟨i, hi⟩ := hcoverA x
    exact ⟨i, interior_subset hi⟩
  obtain ⟨C, hC, htransfer⟩ :=
    exists_probeAtlasC2_transfer_bound (N := N) A A₀ hA hA₀ hAc hA₀c hcover
  obtain ⟨G, hG, hmetric, himmG, hphaseG, hemb, hfinite, hsmall⟩ :=
    exists_sameMetric_phase_embedding_of_gap_probes A hA hAc hcoverA provider
      F hF himm hphase hn hN (div_pos hepsilon hC)
  let b := (probeAtlasCj A 2 (G - F)).toReal
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hbound : probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal b := by
    rw [ENNReal.ofReal_toReal hfinite]
  have houter := htransfer (G - F) (hG.sub hF) b hb hbound
  have houterReal : (probeAtlasCj A₀ 2 (G - F)).toReal ≤ C * b := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top houter
    rwa [ENNReal.toReal_ofReal (mul_nonneg hC.le hb)] at h
  have hstrict : C * b < epsilon := by
    have h := (lt_div_iff₀ hC).mp hsmall
    simpa only [b, mul_comm] using h
  exact ⟨G, hG, hmetric, himmG, hphaseG, hemb,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top houter, houterReal.trans_lt hstrict⟩

/-- One actual compact native atlas is chosen first.  A probes provider on
that atlas upgrades every original immersion, in every subsequently specified
compact smooth atlas C² norm.  Empty, disconnected and nonorientable sources
are retained, and no global tangent-frame premise is used. -/
theorem exists_fixedNativeAtlas_upgrade_in_every_originalAtlas_of_gap_probes
    (hn : 3 ≤ n) (hN : N = n * (n + 1) / 2 + 1) :
    ∃ A : BufferedAtlas M E,
      IsSmoothBufferedAtlas A ∧
      (∀ i, IsCompact (A.support i)) ∧
      (∀ i, A.inner i ⊆ interior (A.support i)) ∧
      (∀ x, ∃ i, x ∈ interior (A.support i)) ∧
      (∀ i, ∃ x : M, A.chart i = chartAt E x) ∧
      (GapControlledUpgradeProbeProvider (N := N) A →
        ∀ (A₀ : BufferedAtlas M E), IsSmoothBufferedAtlas A₀ →
          (∀ i, IsCompact (A₀.support i)) →
          ∀ (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F),
            (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) →
            PhaseRegular F hF → ∀ epsilon : ℝ, 0 < epsilon →
            ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
              (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
              (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
              PhaseRegular G hG ∧ IsClosedEmbedding G ∧
              probeAtlasCj A₀ 2 (G - F) ≠ ⊤ ∧
              (probeAtlasCj A₀ 2 (G - F)).toReal < epsilon) := by
  obtain ⟨A, hA, hcompact, hinner, hcover, hnative⟩ :=
    exists_compact_smooth_bufferedAtlas (M := M) («E» := E)
  refine ⟨A, hA, hcompact, hinner, hcover, hnative, ?_⟩
  intro provider A₀ hA₀ hA₀c F hF himm hphase epsilon hepsilon
  exact exists_originalAtlas_sameMetric_phase_embedding_of_fixed_gap_probes
    A hA hcompact hcover provider A₀ hA₀ hA₀c F hF himm hphase hn hN hepsilon

end GlobalEmbedding.Upgrade
