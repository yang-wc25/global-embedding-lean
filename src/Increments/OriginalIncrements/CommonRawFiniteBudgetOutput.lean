import FaithfulIncrements.RawFiniteBudgetOutput
import OriginalIncrements.CommonMeanNumerics
import OriginalIncrements.CountedPieceBudget

/-!
# The actual original output uses common numerical geometry profiles

One literal counted packet is chosen before q and all finite entrance budgets.
Its total per-phase/owner cardinal bound and center radius are retained from
the same counted primitive, separately from the pointwise overlap bound. Its
low inverse and grid reciprocal radius are aggregated into positive scalars.
The actual mean preparation is reconstructed with common profiles whose
formulas have no Data, chart index, atlas size, or chosen phase functions.
The entrance threshold is exactly commonFiniteThreshold, and is therefore
identical across actual data sharing the displayed original numerical and
low geometric inputs. Manufacture of class-uniform selected phase margins
remains a separate geometric obligation; this theorem does not add it as an
original hypothesis or infer it from qualitative goodness.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion OriginalCollars FaithfulIncrements

universe uM uP
variable {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem raw_common_numeric_finite_budget_output
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
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (Parameter Spatial : ℕ → ℝ)
    (hParameterNonneg : ∀ k, 0 ≤ Parameter k) (hSpatialNonneg : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (Lactive : ℕ)
    (hPrimaryCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu =>
        z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤) :
    ∃ psi : P → ℝ,
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∃ (budgeted : OriginalIncrements.OriginalCountedPrimarySupply Data theta) (cT Mb BInv HGrid : ℝ),
    0 < cT ∧ 0 < Mb ∧ 0 < BInv ∧ 0 < HGrid ∧
    Mb = OriginalIncrements.originalLowPhaseBudget m d
      (fun k => (actualOriginalGivenInputProfile Data k 1).toReal) ∧
    (∀ nu i, budgeted.Mb nu i = Mb) ∧
    (∀ nu i, actualEuclideanPhaseInverseJetCost (budgeted.mu nu i) (budgeted.Mb nu i) 0 0 ≤ BInv) ∧
    (∀ nu i, actualPhaseRefinementFactor (budgeted.mu nu i) (budgeted.Mb nu i) /
      budgeted.buffer nu i ≤ HGrid) ∧
    ∀ (q : ℕ), 1 ≤ q → ∀ (allowed : ℕ → ℝ)
      (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k),
    let J := (q+1)*(q+4)+2
    let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)
    let Theta := commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb BInv HGrid hReserve.reserve_pos
      BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ ell, 0 < ell → ell ≤ 1 →
    (∀ n, n ≤ J → (actualOriginalGivenInputProfile Data n ell).toReal ≤ allowed n) →
    ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
    ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
      G ⊆ incrementsOriginalParameterRegion Data ∧
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
  let LowPacket := fun k => (actualOriginalGivenInputProfile Data k 1).toReal
  obtain ⟨psi,V,hV,hKV,hVU,hOne,hSmooth,hCompact,hSupport,hPart,hCount,hLow⟩ :=
    OriginalIncrements.original_parameter_localization_with_finite_phase_budget Data hd hs B hChart
      BS TS BP TP hBS hTS hBP hTP Ds Dp RS RP hSource hParameter 1 zero_lt_one LowPacket
      (fun k _ => hFinite k) (fun _ _ => le_rfl)
  let theta := fun i => sourceCollarNovParameterLocalized psi
    (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i)
  obtain ⟨counted,hMbEq,hBufferLe⟩ :=
    OriginalIncrements.original_open_counted_primary_supply_from_finite_low_phase_budget
      Data hd hs hp theta hCompact hSmooth hSupport 1 zero_lt_one LowPacket hLow
  let budgeted := counted.toOriginalBudgetedPrimarySupply
  let primary := budgeted.packet
  obtain ⟨profiles⟩ := original_localized_primary_reference_profiles Data hd hs hp hImm B
    BS TS BP TP Ds Dp RS RP psi primary
  obtain ⟨secondary⟩ := fullIncrementNov_original_open_secondary_pieces Data hd hs hp hImm
    theta hCompact hSmooth hSupport
  obtain ⟨secondaryProfiles⟩ := completion_original_secondary_packet_profiles Data hd hs B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial hParameterNonneg
    hSpatialNonneg transition psi secondary
  let Mb := originalLowPhaseBudget m d LowPacket
  have hMb : 0 < Mb := originalLowPhaseBudget_pos m d LowPacket
  obtain ⟨BInv,HGrid,hBInv,hHGrid,hBase,hRatio⟩ := exists_common_packet_low_geometry Data theta budgeted
  refine ⟨psi,counted,profiles.cT,Mb,BInv,HGrid,
    profiles.cT_pos,hMb,hBInv,hHGrid,rfl,hMbEq,hBase,hRatio,?_⟩
  intro q hq allowed hAllowed
  let J := (q+1)*(q+4)+2
  let Packet := actualGivenEnvelope Data J allowed
  let F := commonObserverForward m d Mb Packet Parameter Spatial
  let Inverse := commonObserverInverse m d BInv Packet Parameter Spatial
  let Cutoff := uniformOriginalObserverCutoffProfile m d HGrid BS TS BP TP Parameter Spatial Ds Dp
  let AdaptedMeta := commonAdaptedMeta m d BInv HGrid BS TS BP TP Packet Parameter Spatial Ds Dp
  let conditioned := primary.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
  let Β := Round3ParameterWholePrimaryIndex Data theta conditioned
  let g := round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
  let Forward := commonMeanForward m d Mb Packet Parameter Spatial
  let Meta := commonMeanMeta m d BInv HGrid BS TS BP TP Packet Parameter Spatial Ds Dp
  have hForward : ∀ r, 0 ≤ Forward r := fun _ => round3PreparedFiniteMaximum_nonneg _
  have hMeta : ∀ r, 0 ≤ Meta r := fun _ => round3PreparedFiniteMaximum_nonneg _
  have hInverse : ∀ r, 0 ≤ Inverse r := commonObserverInverse_nonneg m d BInv hBInv.le
    Packet Parameter Spatial hParameterNonneg hSpatialNonneg
  let OldCutoff := originalObserverCutoffProfile Data theta budgeted BS TS BP TP Parameter Spatial Ds Dp
  let OldInverse := originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial
  have hOldCutoff : ∀ r, 0 ≤ OldCutoff r :=
    originalObserverCutoffProfile_nonneg Data theta budgeted BS TS BP TP Parameter Spatial Ds Dp
  have hOldInverse : ∀ r, 0 ≤ OldInverse r :=
    originalBudgetedObserverInverse_nonneg Data theta budgeted Packet Parameter Spatial
  have hChartBounds (r : ℕ) :
      originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial r ≤ F r ∧
      OldInverse r ≤ Inverse r :=
    originalBudgetedObserverProfiles_le_common Data theta budgeted Mb BInv hMb.le hBInv.le
      (fun nu i => (hMbEq nu i).le) hBase Packet Parameter Spatial hParameterNonneg hSpatialNonneg r
  have hCutoffBounds (r : ℕ) : OldCutoff r ≤ Cutoff r :=
    originalObserverCutoffProfile_le_uniform Data theta budgeted HGrid hHGrid.le hRatio
      BS TS BP TP Parameter Spatial hBS hTS hBP hTP hParameterNonneg hSpatialNonneg Ds Dp r
  have hAdaptedBounds (r : ℕ) :
      repairEntranceCompositionProfile OldCutoff OldInverse r ≤ AdaptedMeta r :=
    originalCompositionProfile_mono_prefix OldCutoff OldInverse Cutoff Inverse r hOldCutoff hOldInverse
      (fun k _ => hCutoffBounds k) (fun k _ => (hChartBounds k).2)
  have hPrepared (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (hPrefix : ∀ n, n ≤ J → (actualOriginalGivenInputProfile Data n ell).toReal ≤ allowed n) :
      ∀ i, Nonempty (IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
        (V ×ˢ (univ : Set M)) profiles.cT Inverse Forward Meta
        (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) ell i) := by
    have hGiven := actualGivenEnvelope_current_scale Data J allowed hFinite ell hell1 hPrefix
    have hExact := original_primary_profiles_from_explicit_cutoff_bound_at_scale
      Data hd hs hn B hChart BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial
      hParameterNonneg hSpatialNonneg transition ell hell hell1 Packet
      (fun k => (hGiven k).1) (fun k => (hGiven k).2) psi budgeted profiles OldCutoff hOldCutoff
      (conditioned_original_observer_cutoff_budget Data hd hs hn
        BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP psi V hV hKV hOne
        Parameter Spatial hParameterNonneg hSpatialNonneg transition
        budgeted hCompact hSmooth profiles ell hell.le hell1)
    have hProfiles : OriginalPrimaryPositiveChartProfilesAtScale Data g F Inverse AdaptedMeta ell := by
      intro nu beta i gN t etaN k z hz hPhysical
      have h := hExact nu beta i k z hz hPhysical
      refine ⟨h.1,h.2.1,?_,h.2.2.2.trans (hAdaptedBounds k)⟩
      intro hk
      exact ⟨(h.2.2.1 hk).1.trans (hChartBounds k).1,
        (h.2.2.1 hk).2.trans (hChartBounds k).2⟩
    exact original_conditioned_mean_preparation_from_proved_profiles_at_scale
      Data hd hs hn theta primary profiles V hV hPart ((Ds+1)*(Dp+1)) hCount
      F Inverse AdaptedMeta ell hell hell1 hProfiles
  have hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta) :=
    round3ParameterOriginalPrimaryFamily_preserves Data hd hs hn _ _ _
  have hSourceOpen (nu) (beta : Β) (z : P × M) (hz : z ∈ (g.chart nu beta).source) :
      z.1 ∈ Data.parameterOpen :=
    fullIncrementNov_original_primary_source_parameter_open Data beta.1.2 nu _
      (round3ParameterWholePrimaryPiece Data hd theta conditioned nu beta) z hz
  have hTarget (nu) (beta : Β) (z : P × D) (hz : z ∈ (g.chart nu beta).target) :
      z.1 ∈ Data.parameterOpen :=
    fullIncrementNov_physical_primary_target_parameter_open Data g hPreserves hSourceOpen nu beta z hz
  have hThreshold := commonPreparedThreshold_eq_finite (m := m) (d := d) (N := N) (M := M)
    q (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) Lactive
    rho c profiles.cT Mb BInv HGrid hReserve.reserve_pos
    BS TS BP TP Parameter Spatial Packet allowed Ds Dp hAllowed
    (fun k hk => actualGivenEnvelope_prefix Data J allowed k hk)
  dsimp only
  rw [← hThreshold]
  exact prepared_current_finite_budget_output Data hd hs hn hp hImm hLinear hDecomp
    rho hReserve c hEll Lactive hPrimaryCount Β (fun a => a.1.1)
    g hPreserves hTarget (fun _ => rfl) (fun _ => rfl) V hV hKV
    theta secondary secondaryProfiles
    (fun i z hz => ⟨(hSupport i hz).1.1,mem_univ _⟩)
    hPart ((Ds+1)*(Dp+1)) hCount profiles.cT profiles.cT_pos
    Inverse Forward Meta hInverse hForward hMeta
    (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D))
    q hq allowed hAllowed hFinite
    (fun ell hell hell1 hPrefix i => Classical.choice (hPrepared ell hell hell1 hPrefix i))

/-- A call-compatible complete original outlet whose actual construction uses
the common numerical profiles. The original output contract is unchanged. -/
theorem raw_common_finite_budget_output
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
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (Parameter Spatial : ℕ → ℝ)
    (hParameterNonneg : ∀ k, 0 ≤ Parameter k) (hSpatialNonneg : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (Lactive : ℕ)
    (hPrimaryCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu =>
        z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (q : ℕ) (hq : 1 ≤ q) (allowed : ℕ → ℝ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k)
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤) :
    ∃ (cT : ℝ) (Forward Meta Tinv : ℕ → ℝ) (hForward : ∀ k, 0 ≤ Forward k),
    0 < cT ∧
    let J := (q+1)*(q+4)+2
    let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)
    let P0 := finitePrefixProfile J allowed
    let F0 := finitePrefixProfile J Forward
    let M0 := finitePrefixProfile J Meta
    let I0 := finitePrefixProfile J Tinv
    let hP0 := finitePrefixProfile_nonneg J allowed hAllowed
    let hF0 := finitePrefixProfile_nonneg J Forward (fun k _ => hForward k)
    let Theta := finiteOriginalMeanThreshold.{uM,0} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hReserve.reserve_pos P0 F0 M0 I0 hP0 hF0
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ ell, 0 < ell → ell ≤ 1 →
    (∀ n, n ≤ J → (actualOriginalGivenInputProfile Data n ell).toReal ≤ allowed n) →
    ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
    ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
      G ⊆ incrementsOriginalParameterRegion Data ∧
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
  obtain ⟨psi,budgeted,cT,Mb,BInv,HGrid,hcT,hMb,hBInv,hHGrid,hMbFormula,hMbEq,hBase,hRatio,hOutput⟩ :=
    raw_common_numeric_finite_budget_output Data hd hs hp hn hImm hLinear hDecomp rho hReserve c hEll
      BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP hSource hParameter
      Parameter Spatial hParameterNonneg hSpatialNonneg transition Lactive hPrimaryCount hFinite
  let Packet := actualGivenEnvelope Data ((q+1)*(q+4)+2) allowed
  let Forward := commonMeanForward m d Mb Packet Parameter Spatial
  let Meta := commonMeanMeta m d BInv HGrid BS TS BP TP Packet Parameter Spatial Ds Dp
  let Inverse := commonObserverInverse m d BInv Packet Parameter Spatial
  have hForward : ∀ k, 0 ≤ Forward k := commonMeanForward_nonneg m d Mb Packet Parameter Spatial
  have hActual := hOutput q hq allowed hAllowed
  have hThreshold := commonPreparedThreshold_eq_finite (m := m) (d := d) (N := N) (M := M)
    q (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)) Lactive
    rho c cT Mb BInv HGrid hReserve.reserve_pos
    BS TS BP TP Parameter Spatial Packet allowed Ds Dp hAllowed
    (fun k hk => actualGivenEnvelope_prefix Data _ allowed k hk)
  dsimp only at hActual
  rw [← hThreshold] at hActual
  exact ⟨cT,Forward,Meta,Inverse,hForward,hcT,hActual⟩

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.raw_common_numeric_finite_budget_output

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.raw_common_finite_budget_output
