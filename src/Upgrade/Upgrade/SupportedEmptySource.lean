import Upgrade.CompactUpgradeBudget

/-!
# The original empty-source upgrade branch

For an empty source the original map itself is a smooth closed embedding.
The metric and phase condition are unchanged and the literal original atlas
C² distance is zero. This branch calls no probes or normal-control provider.
-/

noncomputable section
open Set Manifold Module Topology GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The full geometric conclusion of upgrade for an empty original source,
without a probes provider, dimension restriction, orientation or connectedness. -/
theorem exists_sameMetric_phase_embedding_of_empty_source [IsEmpty M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (hphase : PhaseRegular F hF)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (G : M → V) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G),
      (∀ x, inducedMetric (I := IM) G x = inducedMetric (I := IM) F x) ∧
      (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) G x)) ∧
      PhaseRegular G hG ∧ IsClosedEmbedding G ∧
      probeAtlasCj A 2 (G - F) ≠ ⊤ ∧
      (probeAtlasCj A 2 (G - F)).toReal < epsilon := by
  have hinj : Function.Injective F := by
    intro x
    exact isEmptyElim x
  have hzero : probeAtlasCj A 2 (F - F) = 0 :=
    le_antisymm (probeAtlasC2_self_le_zero A hA F hF) bot_le
  refine ⟨F, hF, fun _ ↦ rfl, fun x ↦ isEmptyElim x,
    hphase, hF.continuous.isClosedEmbedding hinj, ?_, ?_⟩
  · simp only [hzero, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
  · simpa only [hzero, ENNReal.toReal_zero] using hepsilon

#print axioms exists_sameMetric_phase_embedding_of_empty_source
end GlobalEmbedding.Upgrade
