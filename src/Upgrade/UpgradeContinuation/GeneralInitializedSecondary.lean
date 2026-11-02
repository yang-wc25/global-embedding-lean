import UpgradeContinuation.OriginalReferenceSupply
import UpgradeContinuation.GeneralInitializedSelected

/-!
# Original F and waves enter the same initialized probe construction

The reference factory is selected once from the original map.  Its exact
seed, primary packet and fixed smoothing packet enter the existing q440
producer together.  The selected primitive profiles, the canonical primary
supplier, and the exact relation of its radius to the chosen buffer are
retained.  The resulting secondary family is the same family as the
initialized closed state.  Every reference choice precedes the probe scale
t; the original contraction by sqrt(1 - delta^2) occurs only inside the
existing producer after those choices have been fixed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation.UpgradeContinuation

universe uM uP
variable {m d N r : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- The complete existing initialized-secondary statement, now with all
reference geometry manufactured from the original map inside the result. -/
def GeneralMapInitializedSecondarySupply
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (waves : Fin r → OpenSupportedLegalWave F hF) : Prop :=
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  ∃ s : OriginalReferenceSupply (m := m) F,
    ∃ B : BufferedAtlas P Ep, ∃ hB : IsSmoothBufferedAtlas B,
    ∃ hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i),
    ∃ Q : Fin B.count → Set Ep,
    ∃ hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i,
    ∃ BP TP : ℕ → ℝ, (∀ k, 0 ≤ BP k) ∧ (∀ k, 0 ≤ TP k) ∧
    ∀ (b : Fin B.count) (p₀ : P) (hpP : p₀ ∈ B.inner b),
      ProbesSelectedGeneralInitializedSecondaryStatement
        (BS := s.fixedClass.numerical.BS) (TS := s.fixedClass.numerical.TS)
        (BP := BP) (TP := TP) (Ds := s.fixedClass.numerical.Ds)
        s.seed s.domain s.smooth s.phase s.freeNormal s.immersion s.parameterSet_eq
        s.baseIndex s.parameter_identity s.refinementMultiplicity s.primary
        s.fixedClass.lower s.fixedClass.numerical.reserve
        s.ellipticity s.linearSmooth s.decomposition s.reserve
        B hB hforward Q (fun i => (hQ i).1) (fun i => (hQ i).2.1)
        hF waves b p₀ hpP

/-- The original smooth phase-regular immersion and the original legal
waves produce the full same-choice q440 initialized-secondary supply. -/
theorem generalMap_exists_initialized_secondary [Nonempty M]
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (himm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hphase : PhaseRegular F hF)
    (waves : Fin r → OpenSupportedLegalWave F hF) :
    GeneralMapInitializedSecondarySupply (m := m) (d := d) (P := P)
      F hF waves := by
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  obtain ⟨s⟩ := exists_originalReference_supply (m := m) hdim hambient F hF himm hphase
  refine ⟨s,?_⟩
  exact probes_exists_general_initialized_closed_state_with_source_and_secondary
    s.seed s.domain s.smooth s.phase s.freeNormal s.immersion s.parameterSet_eq
    s.baseIndex s.parameter_identity s.refinementMultiplicity s.primary
    s.fixedClass.lower s.fixedClass.numerical.reserve
    s.ellipticity s.linearSmooth s.decomposition s.reserve s.fixed
    s.fixed_reference_eq s.fixed_source_domain_eq s.fixed_parameter_domain_eq
    hF waves

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.generalMap_exists_initialized_secondary
