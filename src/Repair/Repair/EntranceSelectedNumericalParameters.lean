import Repair.EntranceFinitePlanAttachment

/-! Pure numerical choices for the actual selected repair factory. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

def repairEntranceSelectedParameters
    (m d N Ds Dp Lprimary : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (normalF normalT secondaryT lower rho C2 Given0 phaseTolerance geometryTolerance tolerance : ℝ)
    (hrho : 0 < rho) (hC2 : 0 ≤ C2) (hPhase : 0 < phaseTolerance)
    (hGeometry : 0 < geometryTolerance) (hTolerance : 0 < tolerance) : RepairEntranceParameters :=
  let base := repairEntranceLowFromMap (m+1) d N C2
  let ML := max base Given0
  let L := ‖actualOriginalCoefficientFunctional (m+1)‖*ML
  have hbase : 0 ≤ base := repairEntranceLowFromMap_nonneg (m+1) d N hC2
  have hML : 0 ≤ ML := hbase.trans (le_max_left _ _)
  have hL : 0 ≤ L := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hML
  { radius := radius
    radius_pos := hradius
    Ds := Ds
    Dp := Dp
    Rsub := (Ds+1)*(Dp+1)*5^Module.finrank ℝ
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
    Lprimary := Lprimary
    Rsecondary := (Ds+1)*(Dp+1)*5^Module.finrank ℝ
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
    budget := 4*(base+1)
    epsilon := min 1 (min phaseTolerance (min geometryTolerance tolerance))
    eta := rho/(4*(L+1))
    budget_pos := by positivity
    epsilon_pos := lt_min (by norm_num) (lt_min hPhase (lt_min hGeometry hTolerance))
    eta_pos := div_pos hrho (by positivity)
    normalF := normalF
    normalT := normalT
    c := lower/4
    cT := normalT/16
    secondaryReserve := secondaryT/16
    meanReserve := rho/4
    meanReserve_pos := div_pos hrho (by norm_num)
    geometryTolerance := geometryTolerance
    linearBound := L
    reserve := rho
    geometryTolerance_pos := hGeometry
    linearBound_nonneg := hL
    reserve_pos := hrho }

def repairEntranceSelectedProfiles
    (BS TS BP TP Inverse Forward Given reference metricReference Meta Kcut Tinv Tobs : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (hReference : ∀ j, 0 ≤ reference j) (hMetric : ∀ j, 0 ≤ metricReference j) :
    RepairEntranceProfiles :=
  { BS := BS, TS := TS, BP := BP, TP := TP, Inverse := Inverse, Forward := Forward
    Given := Given, reference := reference, metricReference := metricReference, Meta := Meta
    Kcut := Kcut, Tinv := Tinv, Tobs := Tobs
    BS_nonneg := hBS, TS_nonneg := hTS, BP_nonneg := hBP, TP_nonneg := hTP
    reference_nonneg := hReference, metricReference_nonneg := hMetric }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceSelectedParameters
