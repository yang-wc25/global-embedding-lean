import IncrementsCompletion.SamplePrimaryOriginalMean
import IncrementsCompletion.AtScalePrimaryAtlas

/-! Actual K, literal finite residual E, and the same final canonical G are
manufactured from current-scale preparation only. The existing raw costs and
finite mean iteration are retained literally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge CollarCompletion
universe uM uP uB
variable {m d N : ℕ} {M : Type uM} {P : Type uP} {Β : Type uB}
  [TopologicalSpace M] [TopologicalSpace P] [Fintype Β]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

private theorem active_trajectory_attach_primary_output
    {E : Type*} {Reserve Profiles Extra : Prop} {Literal Bound : E → Prop}
    (h : Reserve ∧ Profiles ∧ ∃ e, Literal e ∧ Bound e)
    (make : Reserve → Profiles → Extra) :
    Reserve ∧ Profiles ∧ ∃ e, Literal e ∧ Bound e ∧ Extra := by
  obtain ⟨hReserve,hProfiles,e,hLiteral,hBound⟩ := h
  exact ⟨hReserve,hProfiles,e,hLiteral,hBound,make hReserve hProfiles⟩

theorem incrementsCompletion_sample_finite_primary_trajectory
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (Lactive : ℕ)
    (hCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (q Rsub : ℕ) (hq : 1 ≤ q) (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hPacket : ∀ j, (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell i) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W := incrementsOriginalParameterRegion Data
    let hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i :=
      fun _ _ hy => hy.1
    let H := originalFiniteTarget Data hd hs hDecomp ell hell hGiven
    let p := finiteTensorGermSeminorm Data.atlas Data.parameterChart S W hSO ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))
    let hPacket0 := fun j => ENNReal.toReal_nonneg.trans (hPacket j)
    let C := finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let Cdiff := finiteOriginalMeanDifferenceCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let epsilon0 := finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let R := parameterRound2_uniformMeanProfile Packet C (q+4)
    let Bnd := fun s R0 => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R0 Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    let hActive := active_slices_from_original_data Data hd hs g hPreserves hTarget
    0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
    ∃ hsm : actualFiniteMeanMembership Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q,
    let Top := actualFiniteMeanOperator Data.atlas Data.parameterChart S W hSO ell H radius
      (fun p x => Data.F (p,x)) g hActive q hsm
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
    let K := fun i : ℕ => (meanReserveStep (p 0) H radius (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ radius/2) ∧ (∀ i ≤ q, ∀ s, p s (K i) ≤ R i s) ∧
    ∃ E : finiteTensorGermSpace Data.atlas Data.parameterChart S W hSO,
      E.val.val = (fun t x => fullIncrementNovPrimaryMean (fun p x => Data.F (p,x)) g
        (K q).val.val hActive (q+2) (epsilon*ell) t x-Data.H t x) ∧
      (∀ j, p j E ≤ epsilon^(q+1)*finitePhysicalMeanCost Packet C Cdiff q j) ∧
      Nonempty (IncrementsCompletionOriginalPrimaryAtlas Data hd hs g hTarget V0 (K q).val.val
        q Rsub rho ell (epsilon*ell) (fun s => Bnd s (R q (s+(q+4)))) Mg Tfixed) := by
  intro S W hSO H p radius hPacket0 C Cdiff epsilon0 R Bnd Mg Tfixed hActive
  have hMean := incrementsCompletion_sample_actual_mean_tensor Data hd hs hn hp g hPreserves hTarget V0 hV0 hKV0
    hImm ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve Lactive hCount q Rsub hq Packet Tinv Forward Meta
    hTinv hForward hMeta hGiven hPacket prep
  obtain ⟨hepsilon0,hepsilon1,hsm,hTrajectory⟩ := hMean
  refine ⟨hepsilon0,hepsilon1,hsm,?_⟩
  intro Top epsilon he he0 K
  apply active_trajectory_attach_primary_output (hTrajectory epsilon he he0)
  intro hClose hProfile
  have hPacketZero : 0 ≤ Packet 0 := hPacket0 0
  have hradius : 0 < radius := div_pos hReserve.reserve_pos (by positivity)
  have hKreserve : p 0 (K q-H) < radius := (hClose q le_rfl).trans_lt (by linarith)
  have htau : 0 < epsilon*ell := mul_pos he hell
  have htaul : epsilon*ell ≤ ell := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (he0.le.trans hepsilon1) hell.le
  exact incrementsCompletion_at_scale_final_primary_atlas Data hd hs hn hp g hTarget V0 hV0 hKV0
    hImm ell (epsilon*ell) c cT hell hell1 htau htaul hEll hcT hLinear hDecomp rho hReserve q Rsub
    Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep H (K q) rfl hKreserve
    (R q) (hProfile q le_rfl)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_sample_finite_primary_trajectory
