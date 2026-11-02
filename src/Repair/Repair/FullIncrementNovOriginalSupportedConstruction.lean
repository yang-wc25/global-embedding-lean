import Repair.FullIncrementNovSupportedFiniteIncrement
import Repair.FullIncrementNovLocalizedFactories
import Repair.SourceCollarNovOriginalSamples

/-! A concrete original-data construction from the unchanged buffered raw
preparations. The primary packet, actual conditioned geometry, all-order
profiles, parameter collar, signed packet, original compact samples and
original H germ are all produced internally. The given decomposition, phases
and free normals are retained. For every q >= 1 one correction satisfies
all orders at every permitted scale below the constructed threshold.

This is NOT the full original uniform lemma: the threshold is still allowed
to depend on the actual compact low-order geometry. Its reduction to the
original permitted finite numerical prefix remains unproved and is not
silently imposed as an assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem fullIncrementNov_original_actual_supported_construction
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Data.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (q : ℕ) (hq : 1 ≤ q) (Packet : ℕ → ℝ) (hPacket0 : ∀ k, 0 ≤ Packet k) :
    ∃ Theta : ℝ, 0 < Theta ∧ Theta ≤ 1 ∧
    ∃ Cmap Cmetric : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Cmetric j) ∧
    ∀ ell, 0 < ell → ell ≤ 1 →
    (∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤) →
    (∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n) →
    ∀ epsilon, 0 < epsilon → epsilon < Theta → ∀ delta, 0 ≤ delta → delta ≤ epsilon*ell →
    ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧ G ⊆ incrementsOriginalParameterRegion Data ∧
      Round3ParameterJointIncrementConclusion Data.atlas Data.parameterChart
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) G Data.F U Data.H q delta (epsilon*ell) ell Cmap Cmetric ∧
      FullIncrementNovOriginalSupportConclusion Data.cutoff G U := by
  obtain ⟨psi,V,hV,hKV,hVO,hPsi,hOne,hSub,hSupport,hPart,hCount,hGerm,packet,profiles,secondary,hJets⟩ :=
    fullIncrementNov_original_localized_preparations Data hd hs hp hn hImm BS TS BP TP
      hBS hTS hBP hTP Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  let theta := fun i => sourceCollarNovParameterLocalized psi
    (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i)
  let conditioned := packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
  let Β := Round3ParameterWholePrimaryIndex Data theta conditioned
  let g := round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
  obtain ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,hProfiles,hPrepared⟩ :=
    fullIncrementNov_conditioned_open_mean_preparation Data hd hs hn theta packet profiles V hV hPart
      ((Ds+1)*(Dp+1)) hCount hOmega hQ
  let Forward' := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k)
  let Meta' := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)
  let prep := fun i => Classical.choice (hPrepared i)
  have hS := sourceCollarNov_original_evaluation_compact Data hd B hChart RP hOmega hQ
  let H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) (incrementsOriginalParameterRegion Data) :=
    ⟨Data.H,sourceCollarNov_original_target_germ_mem Data hd hs hDecomp _ Subset.rfl⟩
  have hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta) :=
    round3ParameterOriginalPrimaryFamily_preserves Data hd hs hn _ _ _
  have hSourceOpen (nu) (beta : Β) (z : P × M) (hz : z ∈ (g.chart nu beta).source) :
      z.1 ∈ Data.parameterOpen :=
    fullIncrementNov_original_primary_source_parameter_open Data beta.1.2 nu _
      (round3ParameterWholePrimaryPiece Data hd theta conditioned nu beta) z hz
  have hTarget (nu) (beta : Β) (z : P × D) (hz : z ∈ (g.chart nu beta).target) :
      z.1 ∈ Data.parameterOpen :=
    fullIncrementNov_physical_primary_target_parameter_open Data g hPreserves hSourceOpen nu beta z hz
  obtain ⟨Theta,hTheta,hTheta1,Cmap,Cmetric,hCmap,hCmetric,hActual⟩ :=
    fullIncrementNov_actual_supported_finite_increment Data hd hs hn hp hImm hLinear hDecomp rho hReserve c hEll
      hS H rfl Β (fun a => a.1.1) g hPreserves hTarget (fun _ => rfl) (fun _ => rfl)
      V hV hKV theta secondary (fun i z hz => ⟨(hSupport i hz).1.1,mem_univ _⟩)
      hPart ((Ds+1)*(Dp+1)) hCount profiles.cT profiles.cT_pos Inverse Forward' Meta'
      hInverse (fun _ => round3PreparedFiniteMaximum_nonneg _) (fun _ => round3PreparedFiniteMaximum_nonneg _)
      (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) prep q hq Packet hPacket0 (Packet 0) (hPacket0 0)
  refine ⟨Theta,hTheta,hTheta1,Cmap,Cmetric,hCmap,hCmetric,?_⟩
  intro ell hell hell1 hGiven hPacket
  exact hActual ell hell hell1
    (ne_top_of_le_ne_top (hGiven 0) (actualOriginalGivenInputProfile_linear_le Data 0 ell))
    ((ENNReal.toReal_mono (hGiven 0) (actualOriginalGivenInputProfile_linear_le Data 0 ell)).trans (hPacket 0))
    hGiven hPacket

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_actual_supported_construction
