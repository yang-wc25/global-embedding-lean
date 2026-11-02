import NormalPolar.ActualRepairModelFirstDefectPhysical
import NormalPolar.OriginalProbeScales

/-! The actually produced first defect at the original scales and an
explicit initial-scale cap. The cap precedes the actual physical choices;
it chooses a new construction scale inside a supplied cap and never changes
the domain of a probe family which has already been constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation

def actualRepairModelFirstDefectInitialCap (C eta cap : ℝ) : ℝ :=
  min cap (min 1 ((eta/(4*(max C 0+1)))^((5 : ℝ)/24)))

theorem actualRepairModelFirstDefect_initial_cap
    (C eta cap : ℝ) (heta : 0 < eta) (hcap : 0 < cap) :
    0 < actualRepairModelFirstDefectInitialCap C eta cap ∧
    actualRepairModelFirstDefectInitialCap C eta cap ≤ cap ∧
    actualRepairModelFirstDefectInitialCap C eta cap ≤ 1 ∧
    ∀ t, 0 < t → t ≤ actualRepairModelFirstDefectInitialCap C eta cap →
      C*(t^(30 : ℝ)+t^((24 : ℝ)/5)) ≤ eta/2 := by
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  let a := eta/(4*(K+1))
  have ha : 0 < a := div_pos heta (by positivity)
  have hr : 0 < a^((5 : ℝ)/24) := Real.rpow_pos_of_pos ha _
  have hc0 : 0 < actualRepairModelFirstDefectInitialCap C eta cap := by
    exact lt_min hcap (lt_min (by norm_num) hr)
  have hcCap : actualRepairModelFirstDefectInitialCap C eta cap ≤ cap := min_le_left _ _
  have hcOne : actualRepairModelFirstDefectInitialCap C eta cap ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨hc0,hcCap,hcOne,?_⟩
  intro t ht htcap
  have ht1 : t ≤ 1 := htcap.trans hcOne
  have htr : t ≤ a^((5 : ℝ)/24) := htcap.trans ((min_le_right _ _).trans (min_le_right _ _))
  have htp : t^((24 : ℝ)/5) ≤ a := by
    have hh := Real.rpow_le_rpow ht.le htr (by norm_num : 0 ≤ (24 : ℝ)/5)
    have he : (a^((5 : ℝ)/24))^((24 : ℝ)/5) = a := by
      rw [← Real.rpow_mul ha.le]
      norm_num
    exact hh.trans_eq he
  have hpow : t^(30 : ℝ) ≤ t^((24 : ℝ)/5) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have haeq : 4*(K+1)*a = eta := by
    dsimp only [a]
    field_simp
  calc
    C*(t^(30 : ℝ)+t^((24 : ℝ)/5)) ≤ K*(t^(30 : ℝ)+t^((24 : ℝ)/5)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ K*(t^((24 : ℝ)/5)+t^((24 : ℝ)/5)) := by gcongr
    _ ≤ 2*K*a := by nlinarith
    _ ≤ eta/2 := by nlinarith

variable {m d N p r count : ℕ} {M Λ Β SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance scaleFirstTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance scaleFirstTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance scaleFirstTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem actualRepairModelFirstDefect_physical_original_scales
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation atlas param i)
    (H : parameterRound2_originalTensorGermSpace atlas param S W)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (t : Ep) → (x : D) → normalSpace (I := 𝓙) (F t) (c l t x))
    (phase : Fin r → Ep × M → ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (u : Fin p → ℝ)
    (TP meanCost : ℕ → ℝ) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hproduced : ActualRepairModelFirstDefectPhysicalConclusion (SubSecondary := SubSecondary)
      atlas param S W hS hSO H F hF g label c vf phase backgroundLength probeLength a input u
      440 (t^((11 : ℝ)/10)) (t^10) (t^((6 : ℝ)/5)) TP meanCost) :
    ∀ (n j length : ℕ) (MgPiece CH : ℝ)
      (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
        ActualSecondaryPhysicalPieceData F hF n (j+1) (t^((11 : ℝ)/10)) MgPiece CH (t^10) W)
      (hbudget : j+2+length ≤ n) (hql : 440 ≤ length) (hMgPiece : 0 ≤ MgPiece) (hCH : 0 ≤ CH),
    let phases := Sum.elim g.phase phase
    let R0 := round4ParameterProbeCombinedAmplitude F hF g label c vf (t^((6 : ℝ)/5)) (t^10) backgroundLength probeLength a input u false
    let Q0 := round4ParameterProbeCombinedAmplitude F hF g label c vf (t^((6 : ℝ)/5)) (t^10) backgroundLength probeLength a input u true
    let wave := round4ParameterProbeCombinedPrimary F hF g label c vf phase (t^((6 : ℝ)/5)) (t^10) backgroundLength probeLength a input u
    let U := fun z => wave z+actualConstructedSecondarySum F hF (fun rec a => (data rec a).base) (t^((6 : ℝ)/5)) length z
    ∀ (Lmix Rsecondary : ℕ) (M1 CP : ℝ) (Tobs : ℕ → ℝ)
      (obs : ActualRepairModelFirstDefectObservationData atlas param S F hF phases R0 Q0 wave
        n j length (t^((11 : ℝ)/10)) MgPiece CH (t^10) (t^((6 : ℝ)/5)) W data Lmix Rsecondary M1 CP Tobs),
    let C := (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*
      actualFastChartTransferPrefix TP j*
        actualConstructedFiniteErrorCost m N n j length Lmix Rsecondary MgPiece CH M1 CP 0 Tobs+meanCost j
    ∀ (F0 : Ep × M → V) (hF0 : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F0 (b,x))),
      (fun z => F z.1 z.2) = (fun z => Real.sqrt (1-(t^10)^2) • F0 z) →
      H.val = (fun b x => (1-((t^((6 : ℝ)/5))^10/(t^10))^2) • inducedMetric (I := 𝓙) (fun y => F0 (b,y)) x) →
    ∃ normalized : parameterRound2_originalTensorGermSpace atlas param S W,
      normalized.val = (fun b x => (((t^((6 : ℝ)/5))^10)^2)⁻¹ •
        (inducedMetric (I := 𝓙) (fun y => F0 (b,y)) x-
          inducedMetric (I := 𝓙) (fun y => Real.sqrt (1-(t^10)^2) • F0 (b,y)+U (b,y)) x)-
        inducedMetric (I := 𝓙) (fun y => F0 (b,y)) x) ∧
      parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO (t^((6 : ℝ)/5)) j normalized ≤
        C*(t^(30 : ℝ)+t^((24 : ℝ)/5)) := by
  let tau := t^((6 : ℝ)/5)
  let ell := t^((11 : ℝ)/10)
  let delta := t^10
  intro n j length MgPiece CH data hbudget hql hMgPiece hCH phases R0 Q0 wave U
    Lmix Rsecondary M1 CP Tobs obs C F0 hF0 hFzero hHfirst
  have hs := GlobalEmbedding.NormalPolar.probe_original_scale_conditions t ht ht1
  have hDeltaTau : delta ≤ tau := by
    change t^(10 : ℕ) ≤ t^((6 : ℝ)/5)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  obtain ⟨error,herror,hbound,hnormal⟩ := hproduced n j length MgPiece CH data hbudget hql hMgPiece hCH
    hs.2.2.2 (pow_nonneg ht.le 10) hDeltaTau Lmix Rsecondary M1 CP Tobs obs
  obtain ⟨normalized,hval,hnorm⟩ := hnormal F0 hF0 (tau^10)
    (ne_of_gt (pow_pos hs.2.2.1 10)) hFzero hHfirst
  refine ⟨normalized,hval,hnorm.trans_eq ?_⟩
  change ((tau^10)^2)⁻¹*(C*(delta*(tau/ell)^440+delta^3/tau)) = _
  calc
    _ = C*(((tau^10)^2)⁻¹*(delta*(tau/ell)^440+delta^3/tau)) := by ring
    _ = _ := congrArg (fun x : ℝ => C*x) (round4ParameterProbe_first_error_scale_identity ht)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_initial_cap
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_physical_original_scales
