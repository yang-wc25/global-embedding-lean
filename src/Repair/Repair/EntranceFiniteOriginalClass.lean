import Repair.EntranceFiniteSmoothingBounds
import Repair.EntranceFinitePlanAttachment

/-!
# The prescribed finite original class produces the required prefix

The smoothing and geometric profiles are held fixed. The three profiles
which contain reference-map derivatives are completed beyond J by the
actual smooth norms. Their agreement with the prescribed numerical plan
is proved here, and the actual smoothing packet is rebuilt with those
same profiles. Thus no all-orders uniform reference-map bound is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def repairEntranceCompleteReferenceProfiles
    (fixed : RepairEntranceProfiles) (J : ℕ) (actualMetric actualGiven : ℕ → ℝ)
    (hMetric : ∀ j, 0 ≤ actualMetric j) : RepairEntranceProfiles :=
  { fixed with
    Given := repairEntranceFiniteProfile J fixed.Given actualGiven
    reference := repairEntranceFiniteProfile J fixed.reference actualMetric
    metricReference := repairEntranceFiniteProfile J fixed.metricReference actualMetric
    reference_nonneg := repairEntranceFiniteProfile_nonneg J fixed.reference actualMetric
      (fun j _ => fixed.reference_nonneg j) hMetric
    metricReference_nonneg := repairEntranceFiniteProfile_nonneg J fixed.metricReference actualMetric
      (fun j _ => fixed.metricReference_nonneg j) hMetric }

theorem repairEntranceCompleteReferenceProfiles_prefix
    (fixed : RepairEntranceProfiles) (J : ℕ) (actualMetric actualGiven : ℕ → ℝ)
    (hMetric : ∀ j, 0 ≤ actualMetric j) :
    fixed.Prefix (repairEntranceCompleteReferenceProfiles fixed J actualMetric actualGiven hMetric) J := by
  refine ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,
    fun _ _ => rfl,fun _ _ => rfl,?_,?_,?_,fun _ _ => rfl,fun _ _ => rfl,
    fun _ _ => rfl,fun _ _ => rfl⟩
  all_goals intro j hj; exact (repairEntranceFiniteProfile_prefix J _ _ j hj).symm

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius} {reference Given : ℕ → ℝ}

def repairEntranceOriginalClassProfiles
    (fixed : RepairEntranceProfiles) (J : ℕ)
    (packet : Round3RepairFixedSmoothingPacket Data fixed.BS fixed.TS fixed.BP fixed.TP
      Ds Dp radius hradius reference Given) : RepairEntranceProfiles :=
  repairEntranceCompleteReferenceProfiles fixed J packet.closedReferenceProfile
    (fun j => (parameterRound2_originalFixedPacketProfile Data j 1).toReal)
    (fun _ => ENNReal.toReal_nonneg)

/-- This real packet has all-order reference/given bounds, but only the
allowed finite input prefix was constrained. The original physical data,
smooth map, raw preparations and sampling domains are unchanged. -/
def repairEntranceOriginalClassPacket
    (fixed : RepairEntranceProfiles) (J : ℕ) (allowedMap : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J+2 → 0 ≤ allowedMap j)
    (hMetricProfile : ∀ j, j ≤ J → fixed.reference j =
      repairEntranceAllowedMetricProfile (m+1) d N allowedMap j)
    (packet : Round3RepairFixedSmoothingPacket Data fixed.BS fixed.TS fixed.BP fixed.TP
      Ds Dp radius hradius reference Given)
    (hOmega : Data.sourceNormDomain = packet.Omega)
    (hQ : Data.parameterNormDomain = packet.Q) (hAll : Data.parameterSet = univ)
    (hMap : ∀ j, j ≤ J+2 →
      (paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
        packet.closedSamples).toReal ≤ allowedMap j)
    (hGiven : ∀ j, j ≤ J → (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ fixed.Given j) :
    Round3RepairFixedSmoothingPacket Data fixed.BS fixed.TS fixed.BP fixed.TP
      Ds Dp radius hradius (repairEntranceOriginalClassProfiles fixed J packet).reference
      (repairEntranceOriginalClassProfiles fixed J packet).Given :=
  { packet with
    reference_bound := by
      intro j
      have hFiniteMetric := repairEntrance_actual_metric_finite_envelope J allowedMap hAllowed packet hMap
      have hLow (k : ℕ) (hk : k ≤ J) : packet.closedReferenceProfile k ≤ fixed.reference k := by
        rw [hMetricProfile k hk]
        exact (hFiniteMetric.2.1 k).trans_eq (hFiniteMetric.2.2 k hk)
      have hBound := repairEntranceFiniteProfile_dominates J fixed.reference packet.closedReferenceProfile hLow j
      convert hBound using 1
      unfold Round3RepairFixedSmoothingPacket.closedReferenceProfile Round3RepairFixedSmoothingPacket.closedSamples
      rw [hOmega,hQ,hAll,← packet.chart_eq]
      rfl
    given_bound := repairEntranceFiniteProfile_dominates J fixed.Given
      (fun j => (parameterRound2_originalFixedPacketProfile Data j 1).toReal) hGiven }

theorem repairEntranceOriginalClassPacket_prefix_and_envelope
    (fixed : RepairEntranceProfiles) (J : ℕ) (allowedMap : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J+2 → 0 ≤ allowedMap j)
    (hMetricProfile : ∀ j, j ≤ J → fixed.reference j =
      repairEntranceAllowedMetricProfile (m+1) d N allowedMap j)
    (hSameReference : fixed.metricReference = fixed.reference)
    (packet : Round3RepairFixedSmoothingPacket Data fixed.BS fixed.TS fixed.BP fixed.TP
      Ds Dp radius hradius reference Given)
    (hOmega : Data.sourceNormDomain = packet.Omega)
    (hQ : Data.parameterNormDomain = packet.Q) (hAll : Data.parameterSet = univ)
    (hMap : ∀ j, j ≤ J+2 →
      (paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
        packet.closedSamples).toReal ≤ allowedMap j)
    (hGiven : ∀ j, j ≤ J → (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ fixed.Given j) :
    let actual := repairEntranceOriginalClassProfiles fixed J packet
    let bounded := repairEntranceOriginalClassPacket fixed J allowedMap hAllowed hMetricProfile
      packet hOmega hQ hAll hMap hGiven
    fixed.Prefix actual J ∧
    (∀ j, bounded.closedReferenceProfile j ≤ actual.metricReference j) ∧
    bounded.referenceMap = packet.referenceMap ∧ bounded.closedSamples = packet.closedSamples ∧
    bounded.sourcePreparation.raw = packet.sourcePreparation.raw ∧
    bounded.parameterPreparation.raw = packet.parameterPreparation.raw := by
  intro actual bounded
  refine ⟨repairEntranceCompleteReferenceProfiles_prefix fixed J _ _ _,?_,rfl,rfl,rfl,rfl⟩
  intro j
  have hFiniteMetric := repairEntrance_actual_metric_finite_envelope J allowedMap hAllowed packet hMap
  have hLow (k : ℕ) (hk : k ≤ J) : packet.closedReferenceProfile k ≤ fixed.metricReference k := by
    rw [hSameReference,hMetricProfile k hk]
    exact (hFiniteMetric.2.1 k).trans_eq (hFiniteMetric.2.2 k hk)
  exact repairEntranceFiniteProfile_dominates J fixed.metricReference packet.closedReferenceProfile hLow j

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceOriginalClassPacket
#print axioms GlobalEmbedding.Continuation.repairEntranceOriginalClassPacket_prefix_and_envelope
