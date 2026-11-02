import Repair.EntranceFiniteReferenceEnvelope

/-!
# The real smoothing packet consumes the finite reference class

Only the allowed map and original fixed-data prefix is imposed. The actual
smooth higher norms complete both reference profiles after that prefix.
The unchanged cutoff functions, atlas, closed samples and reference map
are copied into the original smoothing packet, which therefore supplies
all subsequent actual stage estimates with these chosen profiles.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

def repairEntranceFiniteMetricReference
    (J : ℕ) (allowedMap : ℕ → ℝ)
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket) :
    ℕ → ℝ :=
  repairEntranceFiniteProfile J (repairEntranceAllowedMetricProfile (m+1) d N allowedMap)
    packet.closedReferenceProfile

def repairEntranceFiniteGiven (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (J : ℕ) (allowedGiven : ℕ → ℝ) : ℕ → ℝ :=
  repairEntranceFiniteProfile J allowedGiven (fun j => (parameterRound2_originalFixedPacketProfile Data j 1).toReal)

/-- Actual all-order bounds are completed from smooth input after fixing
the permitted finite prefix. No smoothing function or norm sample changes. -/
def repairEntranceFiniteSmoothingPacket
    (J : ℕ) (allowedMap allowedGiven : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J+2 → 0 ≤ allowedMap j)
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hOmega : Data.sourceNormDomain = packet.Omega)
    (hQ : Data.parameterNormDomain = packet.Q) (hAll : Data.parameterSet = univ)
    (hMap : ∀ j, j ≤ J+2 →
      (paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
        packet.closedSamples).toReal ≤ allowedMap j)
    (hGiven : ∀ j, j ≤ J → (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ allowedGiven j) :
    Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius
      (repairEntranceFiniteMetricReference J allowedMap packet) (repairEntranceFiniteGiven Data J allowedGiven) :=
  { packet with
    reference_bound := by
      intro j
      have hBound := (repairEntrance_actual_metric_finite_envelope J allowedMap hAllowed packet hMap).2.1 j
      change packet.closedReferenceProfile j ≤ repairEntranceFiniteMetricReference J allowedMap packet j at hBound
      convert hBound using 1
      unfold Round3RepairFixedSmoothingPacket.closedReferenceProfile Round3RepairFixedSmoothingPacket.closedSamples
      rw [hOmega,hQ,hAll,← packet.chart_eq]
    given_bound := repairEntranceFiniteProfile_dominates J allowedGiven
      (fun j => (parameterRound2_originalFixedPacketProfile Data j 1).toReal) hGiven }

theorem repairEntranceFiniteSmoothingPacket_actual
    (J : ℕ) (allowedMap allowedGiven : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J+2 → 0 ≤ allowedMap j)
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hOmega : Data.sourceNormDomain = packet.Omega)
    (hQ : Data.parameterNormDomain = packet.Q) (hAll : Data.parameterSet = univ)
    (hMap : ∀ j, j ≤ J+2 →
      (paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
        packet.closedSamples).toReal ≤ allowedMap j)
    (hGiven : ∀ j, j ≤ J → (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ allowedGiven j) :
    let bounded := repairEntranceFiniteSmoothingPacket J allowedMap allowedGiven hAllowed packet hOmega hQ hAll hMap hGiven
    bounded.referenceMap = packet.referenceMap ∧ bounded.closedSamples = packet.closedSamples ∧
    bounded.sourcePreparation.raw = packet.sourcePreparation.raw ∧
    bounded.parameterPreparation.raw = packet.parameterPreparation.raw ∧
    bounded.closedReferenceProfile = packet.closedReferenceProfile ∧
    (∀ j, j ≤ J → repairEntranceFiniteMetricReference J allowedMap packet j =
      repairEntranceAllowedMetricProfile (m+1) d N allowedMap j) ∧
    (∀ j, j ≤ J → repairEntranceFiniteGiven Data J allowedGiven j = allowedGiven j) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · exact repairEntranceFiniteProfile_prefix J _ _
  · exact repairEntranceFiniteProfile_prefix J _ _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceFiniteSmoothingPacket
#print axioms GlobalEmbedding.Continuation.repairEntranceFiniteSmoothingPacket_actual
