import Repair.EntranceReferenceMetric
import Repair.EntranceReferenceEnvelopeCosts

/-!
# A reference envelope manufactured from a finite original map class

The allowed prefix is fixed before the reference map. Beyond that prefix
the actual smooth map may have arbitrary derivatives: its finite actual
norms are used only to complete the later-stage profile. The actual
reference tensor is bounded on precisely the original closed samples.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def repairEntranceFiniteProfile (J : ℕ) (allowed actual : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ J then allowed j else actual j

theorem repairEntranceFiniteProfile_prefix (J : ℕ) (allowed actual : ℕ → ℝ)
    (j : ℕ) (hj : j ≤ J) : repairEntranceFiniteProfile J allowed actual j = allowed j := by
  simp only [repairEntranceFiniteProfile,if_pos hj]

theorem repairEntranceFiniteProfile_dominates (J : ℕ) (allowed actual : ℕ → ℝ)
    (hPrefix : ∀ j, j ≤ J → actual j ≤ allowed j) (j : ℕ) :
    actual j ≤ repairEntranceFiniteProfile J allowed actual j := by
  unfold repairEntranceFiniteProfile
  split_ifs with h
  · exact hPrefix j h
  · exact le_rfl

theorem repairEntranceFiniteProfile_nonneg (J : ℕ) (allowed actual : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J → 0 ≤ allowed j) (hActual : ∀ j, 0 ≤ actual j) (j : ℕ) :
    0 ≤ repairEntranceFiniteProfile J allowed actual j := by
  unfold repairEntranceFiniteProfile
  split_ifs with h
  · exact hAllowed j h
  · exact hActual j

def repairEntranceAllowedMetricProfile (n d N : ℕ) (mapBound : ℕ → ℝ) (j : ℕ) : ℝ :=
  repairEntranceMetricCost n d N j*(mapBound (j+2))^2

theorem repairEntranceAllowedMetricProfile_nonneg (n d N : ℕ) (mapBound : ℕ → ℝ) (j : ℕ) :
    0 ≤ repairEntranceAllowedMetricProfile n d N mapBound j :=
  mul_nonneg (repairEntranceMetricCost_nonneg n d N j) (sq_nonneg _)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
private local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- A bound for the actual reference metric is produced from the prescribed
finite map bounds. There is no all-orders uniform hypothesis on the map. -/
theorem repairEntrance_actual_metric_finite_envelope
    (J : ℕ) (allowedMap : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ J+2 → 0 ≤ allowedMap j)
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (hMap : ∀ j, j ≤ J+2 →
      (paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        packet.referenceMap) (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart)
        packet.closedSamples).toReal ≤ allowedMap j) :
    let allowedMetric := repairEntranceAllowedMetricProfile (m+1) d N allowedMap
    let envelope := repairEntranceFiniteProfile J allowedMetric packet.closedReferenceProfile
    (∀ j, 0 ≤ envelope j) ∧
    (∀ j, packet.closedReferenceProfile j ≤ envelope j) ∧
    (∀ j, j ≤ J → envelope j = allowedMetric j) := by
  intro allowedMetric envelope
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hSmooth := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hFinite (j : ℕ) := parameterRound2_paperAtlasCj_finite_of_compact
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart packet.referenceMap)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    packet.closedSamples_compact (fun _ _ hy => hy.1) hSmooth j
  have hBound (j : ℕ) (hj : j ≤ J) : packet.closedReferenceProfile j ≤ allowedMetric j := by
    exact (repairEntrance_inducedMetric_Cj_le Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB packet.closedSamples (fun _ _ hy => hy.1)
      packet.referenceMap packet.referenceMap_smooth j (allowedMap (j+2))
      (hAllowed (j+2) (by omega)) (hFinite (j+2)) (hMap (j+2) (by omega))).2
  exact ⟨repairEntranceFiniteProfile_nonneg J allowedMetric packet.closedReferenceProfile
      (fun j _ => repairEntranceAllowedMetricProfile_nonneg (m+1) d N allowedMap j)
      (fun _ => ENNReal.toReal_nonneg),
    repairEntranceFiniteProfile_dominates J allowedMetric packet.closedReferenceProfile hBound,
    repairEntranceFiniteProfile_prefix J allowedMetric packet.closedReferenceProfile⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_metric_finite_envelope
