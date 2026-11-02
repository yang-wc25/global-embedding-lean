import Upgrade.IncidenceNormalControl

/-!
# Explicit upstream boundary for the finite geometric upgrade chain

This internal proposition asks the upstream construction for the original
full probes conclusion, together with the two quantitative consequences of
its chosen polar normal identification. It is called anew for every current
actual immersion and the finite actual wave list prepared from its current
bad set. It asserts no incidence rank, avoidance, injectivity, or upgrade.

There is deliberately no proof of this proposition in this candidate. The
original upgrade target is unchanged and remains dependent on the upstream
construction. A theorem taking this proposition is only a conditional
geometric consumer, never acceptance of the original target.
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

def ControlledUpgradeProbeProvider (A : BufferedAtlas M E) : Prop :=
  ∀ (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F),
    (∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) F x)) → PhaseRegular F hF →
    ∀ (r : ℕ) (waves : Fin r → LocalLegalWave F hF),
      ∃ probe : ExactProbeFamily F hF A waves, Nonempty (ChosenProbeNormalControl probe)

end GlobalEmbedding.Upgrade
