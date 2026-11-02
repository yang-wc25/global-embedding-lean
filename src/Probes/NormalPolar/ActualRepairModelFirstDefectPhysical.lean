import NormalPolar.ActualRepairModelFirstDefectObservation
import NormalPolar.ActualRepairModelFirstDefectAssembly

/-! Concrete result type for the same combined increment. Packaging this
large dependent conclusion keeps every declaration within the default Lean
checking budget. No estimated quantity occurs as a record input: the full
metric error and its normalized first defect are outputs of the theorem below.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
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
private local instance physicalFirstTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance physicalFirstTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance physicalFirstTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

/-- The same physical choices produce one complete error and its literal
contracted first-map normalization. This is an output proposition, not an
interface whose fields assume those outputs. -/
def ActualRepairModelFirstDefectPhysicalConclusion
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
  (q : ℕ) (ell delta tau : ℝ) (TP meanCost : ℕ → ℝ) : Prop :=
    ∀ (n j length : ℕ) (MgPiece CH : ℝ)
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData F hF n (j+1) ell MgPiece CH delta W)
    (hbudget : j+2+length ≤ n) (hql : q ≤ length)
    (hMgPiece : 0 ≤ MgPiece) (hCH : 0 ≤ CH)
    (hTauEll : tau ≤ ell) (hDeltaNonneg : 0 ≤ delta) (hDeltaTau : delta ≤ tau),
    let phases := Sum.elim g.phase phase
    let R0 := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
    let Q0 := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
    let wave := round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u
    let U := fun z => wave z+actualConstructedSecondarySum F hF (fun rec a => (data rec a).base) tau length z
    ∀ (Lmix Rsecondary : ℕ) (M1 CP : ℝ) (Tobs : ℕ → ℝ)
      (obs : ActualRepairModelFirstDefectObservationData atlas param S F hF phases R0 Q0 wave
        n j length ell MgPiece CH delta tau W data Lmix Rsecondary M1 CP Tobs),
    let CR := (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*
      actualFastChartTransferPrefix TP j*
        actualConstructedFiniteErrorCost m N n j length Lmix Rsecondary MgPiece CH M1 CP 0 Tobs
    let CM := meanCost j
    ∃ error : parameterRound2_originalTensorGermSpace atlas param S W,
      error.val = incrementsOriginalMetricError (fun z => F z.1 z.2) U H.val delta ∧
      parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO tau j error ≤
        (CR+CM)*(delta*(tau/ell)^q+delta^3/tau) ∧
      ∀ (F0 : Ep × M → V) (hF0 : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => F0 (t,x)))
        (delta1 : ℝ), delta1 ≠ 0 →
        (fun z => F z.1 z.2) = (fun z => Real.sqrt (1-delta^2) • F0 z) →
        H.val = (fun t x => (1-(delta1/delta)^2) • inducedMetric (I := 𝓙) (fun y => F0 (t,y)) x) →
      ∃ normalized : parameterRound2_originalTensorGermSpace atlas param S W,
        normalized.val = (fun t x => (delta1^2)⁻¹ •
          (inducedMetric (I := 𝓙) (fun y => F0 (t,y)) x-
            inducedMetric (I := 𝓙) (fun y => Real.sqrt (1-delta^2) • F0 (t,y)+U (t,y)) x)-
          inducedMetric (I := 𝓙) (fun y => F0 (t,y)) x) ∧
        parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO tau j normalized ≤
          (delta1^2)⁻¹*((CR+CM)*(delta*(tau/ell)^q+delta^3/tau))

theorem actualRepairModelFirstDefect_physical_from_mean
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
  (q : ℕ) (ell delta tau : ℝ) (TP meanCost : ℕ → ℝ)
    (hAtlas : IsSmoothBufferedAtlas atlas)
    (hParamSmooth : ∀ i, param i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (hW : IsOpen W) (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau)
    (hdelta : delta ≠ 0) (hTP : ∀ k, 0 ≤ TP k) (hCost : ∀ j, 0 ≤ meanCost j)
    (hParam : ∀ i : Fin atlas.count × Fin count, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (param i.2)) z‖ ≤ TP k)
    (Mean : parameterRound2_originalTensorGermSpace atlas param S W)
    (hMeanVal : Mean.val = (fun t x => round4ParameterProbeCombinedMean F hF g label c vf phase
      tau delta backgroundLength probeLength a input u t x-delta^2 • H.val t x))
    (hMeanBound : ∀ j, parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO ell j Mean ≤
      delta^2*((tau/ell)^(q+1)*meanCost j)) :
    ActualRepairModelFirstDefectPhysicalConclusion (SubSecondary := SubSecondary)
      atlas param S W hS hSO H F hF g label c vf phase backgroundLength probeLength a input u q ell delta tau TP meanCost := by
  intro n j length MgPiece CH data hbudget hql hMgPiece hCH hTauEll hDeltaNonneg hDeltaTau
    phases R0 Q0 wave U Lmix Rsecondary M1 CP Tobs obs CR CM
  obtain ⟨hRest,hRestFinite,hRestBound⟩ := actualRepairModelFirstDefect_combined_original_remainder
    atlas param hAtlas hParamSmooth S hSO F hF g label c vf phase backgroundLength probeLength a input u
    n j q length ell MgPiece CH delta tau W data hbudget hql hell hell1 htau hTauEll
    hDeltaNonneg hDeltaTau hMgPiece hCH hW
    obs.K obs.hprimary obs.Omega obs.hOmega obs.hSample obs.hTarget obs.hmap obs.binding obs.O obs.hO
    obs.hOOmega obs.hActive obs.hSource obs.hTransition Tobs obs.hT obs.hSecondarySample obs.hTransitionBound
    Lmix Rsecondary obs.hL obs.hR M1 CP obs.hM1 obs.hCP obs.hFobs obs.hU1 obs.hLin obs.hMean obs.hGrouped
    obs.hU1jet obs.hLinJet TP hTP (fun i z hz k hk _ => hParam i z hz k hk)
  let Rest : parameterRound2_originalTensorGermSpace atlas param S W :=
    ⟨actualRepairModelFirstDefectArrayRest (fun z => F z.1 z.2) U phases tau R0 Q0,hRest⟩
  have hMeanArray : Mean.val = round4ParameterProbeArrayMean (I := 𝓙) phases tau R0 Q0-delta^2 • H.val := by
    exact hMeanVal
  obtain ⟨error,herror,herrorBound⟩ := actualRepairModelFirstDefect_same_array_germ_add
    atlas param S W hS hSO (fun z => F z.1 z.2) U phases R0 Q0 H.val j q delta tau ell CR CM
    hDeltaNonneg hDeltaTau htau hTauEll hell1 (hCost j) Rest Mean rfl hMeanArray hRestBound (hMeanBound j)
  refine ⟨error,herror,herrorBound,?_⟩
  intro F0 hF0 delta1 hdelta1 hFzero hHfirst
  have hsmall : delta^2 ≤ 1 := by
    have hd1 : delta ≤ 1 := hDeltaTau.trans (hTauEll.trans hell1)
    nlinarith
  have he := herror
  rw [hFzero,hHfirst] at he
  exact actualRepairModelFirstDefect_normalize_produced_error atlas param S W hS hSO
    F0 U hF0 delta delta1 hdelta hdelta1 hsmall error he tau
    ((CR+CM)*(delta*(tau/ell)^q+delta^3/tau)) j herrorBound

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_physical_from_mean
