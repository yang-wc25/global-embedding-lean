import Round2.ProbeNormalGap
import Upgrade.CompactProbeProvider

/-!
# Exact probes and the selected zeroth-order normal gap

This is the explicit remaining provider for the DQ-free upgrade geometry.
It retains the same full `ExactProbeFamily`, the same current immersion and
the same prepared finite legal wave list.  Only the unneeded quantitative
spatial derivative of Q is removed from the auxiliary normal-control record.

No incidence rank, avoidance, good parameter, injection or embedding conclusion
is a field.  The actual provider is still upstream; its definition is not its
construction and cannot be counted as completion of the original target.
-/

noncomputable section
open Bundle Manifold
open scoped ContDiff

namespace GlobalEmbedding.Upgrade
open Paper

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

def GapControlledUpgradeProbeProvider (A : BufferedAtlas M E) : Prop :=
  ∀ (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F),
    (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) → PhaseRegular F hF →
    ∀ (r : ℕ) (waves : Fin r → LocalLegalWave F hF),
      ∃ probe : ExactProbeFamily F hF A waves, Nonempty (ChosenProbeNormalGap probe)

/-- Every previously admitted stronger provider is accepted by the new chain;
the implication uses the very same probe family and chosen identification. -/
theorem ControlledUpgradeProbeProvider.toGap
    (A : BufferedAtlas M E) (provider : ControlledUpgradeProbeProvider (N := N) A) :
    GapControlledUpgradeProbeProvider (N := N) A := by
  intro F hF himm hphase r waves
  obtain ⟨probe, ⟨control⟩⟩ := provider F hF himm hphase r waves
  exact ⟨probe, ⟨control.toGap⟩⟩

end GlobalEmbedding.Upgrade
