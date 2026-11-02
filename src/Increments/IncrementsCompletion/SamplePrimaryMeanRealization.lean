import IncrementsCompletion.SamplePrimaryTrajectory
import IncrementsCompletion.FiniteMeanRealization

/-! Current-scale primitive preparation manufactures the unchanged actual
mean realization package. Its input remains literally the q substitutions
of the original H and the same physical mean error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

private theorem active_realize_finite_trajectory
    {E : Type*} {Reserve Profiles Raw Result : Prop} {Literal Bound : E → Prop}
    (h : Reserve ∧ Profiles ∧ ∃ e, Literal e ∧ Bound e ∧ Raw)
    (make : Reserve → Profiles → ∀ e, Literal e → Bound e → Raw → Result) : Result := by
  obtain ⟨hReserve,hProfiles,e,hLiteral,hBound,hRaw⟩ := h
  exact make hReserve hProfiles e hLiteral hBound hRaw

theorem incrementsCompletion_sample_finite_mean_realization
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
    let hPacket0 := fun j => ENNReal.toReal_nonneg.trans (hPacket j)
    let C := finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let Cdiff := finiteOriginalMeanDifferenceCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let epsilon0 := finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos Packet Forward Meta Tinv hPacket0 hForward
    let R := parameterRound2_uniformMeanProfile Packet C (q+4)
    let Bnd := fun s => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) (R q (s+(q+4))) Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    let hActive := active_slices_from_original_data Data hd hs g hPreserves hTarget
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 →
      Nonempty (IncrementsCompletionFiniteMeanRealization Data hd hs g hTarget hActive V0
        q Rsub rho ell (epsilon*ell) (finitePhysicalMeanCost Packet C Cdiff q) Bnd Mg Tfixed) := by
  intro hPacket0 C Cdiff epsilon0 R Bnd Mg Tfixed hActive epsilon he he0
  have hFull := incrementsCompletion_sample_finite_primary_trajectory Data hd hs hn hp g
    hPreserves hTarget V0 hV0 hKV0 hImm ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve
    Lactive hCount q Rsub hq Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep
  obtain ⟨hepsilon0,hepsilon1,hsm,hTrajectory⟩ := hFull
  let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
    Data.parameterNormDomain Data.parameterSet
  let W := incrementsOriginalParameterRegion Data
  let hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i :=
    fun _ _ hy => hy.1
  let H := originalFiniteTarget Data hd hs hDecomp ell hell hGiven
  let p := finiteTensorGermSeminorm Data.atlas Data.parameterChart S W hSO ell
  let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))
  have hradius : 0 < radius := div_pos hReserve.reserve_pos (by have h0 := hPacket0 0; positivity)
  let Top := actualFiniteMeanOperator Data.atlas Data.parameterChart S W hSO ell H radius
    (fun p x => Data.F (p,x)) g hActive q hsm
  let K := fun i : ℕ => (meanReserveStep (p 0) H radius (Top epsilon))^[i] H
  apply active_realize_finite_trajectory (hTrajectory epsilon he he0)
  intro hClose hProfile E hE hEbound hPrimary
  obtain ⟨primary⟩ := hPrimary
  have hFormula := incrementsCompletion_actual_trajectory_eq_literal Data.atlas Data.parameterChart
    S W hSO ell H radius hradius (fun p x => Data.F (p,x)) g hActive q hsm epsilon he
    (he0.le.trans hepsilon1) hClose q le_rfl
  refine ⟨{
    input := (K q).val.val
    input_formula := hFormula
    residual := E
    literal := hE
    bound := ?_
    primary := primary }⟩
  intro j
  have hRatio : (epsilon*ell)/ell = epsilon := mul_div_cancel_right₀ epsilon hell.ne'
  rw [hRatio,mul_comm]
  exact hEbound j

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_sample_finite_mean_realization
