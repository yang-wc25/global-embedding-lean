import IncrementsCompletion.SampleDataUniformPreparedIncrement
import IncrementsCompletion.ExactOriginalOrderOutput

/-! Exact original scale/order estimates with one C before all actual
current-scale primary and secondary preparations and their finite indices.
Same U, literal original F/H/norm domains/supports, all j, finite norms.
Uniform primitive budget and original collar production remain upstream;
this is not acceptance of the complete original theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge CollarCompletion
universe uM uP uB
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance incrementsSampleDataUniformOriginalScaleSignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem incrementsCompletion_sample_data_uniform_original_output
    (rho : ℝ) (hrho : 0 < rho) (c : ℝ)
    (L : ℕ)
    (secondaryReserve : ℝ) (hSecondaryReserve : 0 < secondaryReserve)
    (SecondaryInverse SecondaryCutoff SecondaryObserver : ℕ → ℝ)
    (hSecondaryInverse : ∀ k, 0 ≤ SecondaryInverse k)
    (hSecondaryCutoff : ∀ k, 0 ≤ SecondaryCutoff k)
    (hSecondaryObserver : ∀ k, 0 ≤ SecondaryObserver k)
    (cT : ℝ) (hcT : 0 < cT) (Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (Rsub Lactive : ℕ)
    (q : ℕ) (hq : 1 ≤ q) (Packet : ℕ → ℝ) (hPacket0 : ∀ k, 0 ≤ Packet k)
    :
    let Theta := finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hrho Packet Forward Meta Tinv hPacket0 hForward
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ (P : Type uP) [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c),
    ∀ (_hPrimaryCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive),
    ∀ ell, 0 < ell → ell ≤ 1 →
    (∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤) →
    (∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n) →
    ∀ (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z : P × M, z.1 ∈ V0 → ∑ i, theta i z = 1)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (hMargin : ∀ r i (a : secondary.s r i), secondaryReserve ≤ (secondary.piece r i a).cT)
    (secondaryProfiles : IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta secondary ell
      SecondaryInverse SecondaryCutoff SecondaryObserver),
    ∀ (Β : Type uB) [Fintype Β] (primaryHost : Β → Fin Data.atlas.count)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (hPhase : ∀ nu, g.phase nu = Data.phase nu) (hCutoff : ∀ nu, g.cutoff nu = Data.cutoff nu)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell i),
    ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
    ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧ G ⊆ incrementsOriginalParameterRegion Data ∧
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ U G ∧
      FullIncrementNovOriginalSupportConclusion Data.cutoff G U ∧
      ∀ j, paperAtlasWeighted 0 j tau
        (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) ≠ ⊤ ∧
        (paperAtlasWeighted 0 j tau
          (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
          (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
          (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet)).toReal ≤ C j*delta*tau ∧
        paperAtlasWeighted 0 j tau
          (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
            (incrementsOriginalMetricError Data.F U Data.H delta))
          (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
          (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet) ≠ ⊤ ∧
        (paperAtlasWeighted 0 j tau
          (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
            (incrementsOriginalMetricError Data.F U Data.H delta))
          (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
          (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet)).toReal ≤
          C j*(delta*(tau/ell)^q+delta^3/tau) := by
  intro Theta
  obtain ⟨hTheta,hTheta1,Cmap,Cmetric,hCmap,hCmetric,hActual⟩ :=
    incrementsCompletion_sample_data_uniform_prepared_increment.{uM,uP,uB}
      (m := m) (d := d) (N := N) (M := M) rho hrho c L secondaryReserve hSecondaryReserve
      SecondaryInverse SecondaryCutoff SecondaryObserver hSecondaryInverse hSecondaryCutoff hSecondaryObserver
      cT hcT Tinv Forward Meta
      hTinv hForward hMeta Rsub Lactive q hq Packet hPacket0
  let C := fun j => max (Cmap j) (Cmetric j)
  refine ⟨hTheta,hTheta1,C,fun j => (hCmap j).trans (le_max_left _ _),?_⟩
  intro P _ _ _ Data hd hs hn hp hImm hLinear hDecomp hReserve hEll hPrimaryCount ell hell hell1 hGiven hPacket V0 hV0 hKV0 theta secondary hSupport hPart hCount hMargin
    secondaryProfiles Β _ primaryHost g hPreserves hTarget hPhase hCutoff prep
    tau delta hdelta hdt htaul hRatio
  have htau : 0 < tau := hdelta.trans_le hdt
  have hCancel : (tau/ell)*ell = tau := div_mul_cancel₀ tau hell.ne'
  obtain ⟨G,U,hG,hKG,hGR,hJoint,hSupport⟩ :=
    hActual P Data hd hs hn hp hImm hLinear hDecomp hReserve hEll hPrimaryCount ell hell hell1 hGiven hPacket V0 hV0 hKV0 theta secondary hSupport hPart hCount hMargin
      secondaryProfiles Β primaryHost g hPreserves hTarget hPhase hCutoff prep (tau/ell) (div_pos htau hell) hRatio delta
      hdelta.le (by simpa only [hCancel] using hdt)
  rw [hCancel] at hJoint
  have hExact := incrementsCompletion_exact_original_order_estimates Data.atlas Data.parameterChart
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet) G Data.F U Data.H q delta tau ell
    hdelta.le htau hell Cmap Cmetric hCmap hJoint
  exact ⟨G,U,hG,hKG,hGR,hJoint.joint_smooth,hSupport,fun j => (hExact j).2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_sample_data_uniform_original_output
