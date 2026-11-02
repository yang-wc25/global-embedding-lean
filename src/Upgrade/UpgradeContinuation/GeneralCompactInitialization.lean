import UpgradeContinuation.GeneralInitializedSecondary
import NormalPolar.ActualRepairCompactParameterModel
import Probes.Round4OriginalProbeParameters

/-!
# The original input chooses its compact parameter manifold and base chart

The existing unit-sphere model supplies a genuine compact parameter manifold
in dimension card(Fin r × Bool), including r = 0.  The initialized producer
chooses its globally smooth forward charts and all compact samples on this
manifold.  Its cover then supplies an actual base chart at the fixed sphere
base point.  The already established round4PairedParameterIndex provides
the original labels with the exact Pi-norm isometry.

Thus the entrance below has no parameter manifold, atlas, forward-chart
smoothness, compact sample, base chart, or base point among its inputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- The same selected initialized supply on a fully manufactured compact
parameter model, with an actual base chart chosen inside the conclusion. -/
def GeneralCompactInitializedSecondarySupply
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (waves : Fin r → OpenSupportedLegalWave F hF) : Prop :=
  let d := Fintype.card (Fin r × Bool)
  let P := ActualRepairCompactParameter d
  let p₀ := actualRepairCompactParameterBase d
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  ∃ s : OriginalReferenceSupply (m := m) F,
    ∃ B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)),
    ∃ hB : IsSmoothBufferedAtlas B,
    ∃ hforward : ∀ i, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin d))
      𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ (B.chart i),
    ∃ Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)),
    ∃ hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i,
    ∃ BP TP : ℕ → ℝ, (∀ k, 0 ≤ BP k) ∧ (∀ k, 0 ≤ TP k) ∧
    ∃ b : Fin B.count, ∃ hp₀ : p₀ ∈ B.inner b,
      ProbesSelectedGeneralInitializedSecondaryStatement
        (BS := s.fixedClass.numerical.BS) (TS := s.fixedClass.numerical.TS)
        (BP := BP) (TP := TP) (Ds := s.fixedClass.numerical.Ds)
        s.seed s.domain s.smooth s.phase s.freeNormal s.immersion s.parameterSet_eq
        s.baseIndex s.parameter_identity s.refinementMultiplicity s.primary
        s.fixedClass.lower s.fixedClass.numerical.reserve
        s.ellipticity s.linearSmooth s.decomposition s.reserve
        B hB hforward Q (fun i => (hQ i).1) (fun i => (hQ i).2.1)
        hF waves b p₀ hp₀

/-- The original F and legal waves alone choose every source and parameter
input for the same q440 closed-state producer.  The positive repair numbers
are universally quantified only after the physical packet has been fixed. -/
theorem generalMap_exists_compact_initialized_secondary [Nonempty M]
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hphase : PhaseRegular F hF)
    (waves : Fin r → OpenSupportedLegalWave F hF) :
    GeneralCompactInitializedSecondarySupply (m := m) F hF waves := by
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  obtain ⟨s,B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,hAt⟩ :=
    generalMap_exists_initialized_secondary
      (m := m) (d := Fintype.card (Fin r × Bool))
      (P := ActualRepairCompactParameter (Fintype.card (Fin r × Bool)))
      hdim hambient F hF himm hphase waves
  obtain ⟨b,hb⟩ := B.cover (actualRepairCompactParameterBase (Fintype.card (Fin r × Bool)))
  exact ⟨s,B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,b,hb,hAt b _ hb⟩

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.GeneralCompactInitializedSecondarySupply
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.generalMap_exists_compact_initialized_secondary
