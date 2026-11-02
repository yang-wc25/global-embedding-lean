import OriginalIncrements.CommonGeometryRawOutput
import OriginalIncrements.CommonSecondaryPreparedOutput
import OriginalIncrements.CommonGeometryPrimarySupply
import FaithfulIncrements.RawFiniteBudgetOutput
import OriginalIncrements.CommonMeanNumerics
import OriginalIncrements.CountedPieceBudget
import OriginalIncrements.FixedPhaseLowBudget

/-!
# The same raw increment consumes common primary and secondary numbers

The primary counted grid is built at the same common mu/Mb/radius/buffer.
The actual signed-secondary packet is the one supplied by the proved
numerical factory, with its common reserve and all-order profiles. Both
packets enter the same mean, solver, supports and all-order displacement.
This internal consumer never selects a secondary reserve or derivative
profile by taking a maximum after seeing the datum.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
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


theorem localized_raw_common_geometry_secondary_budget_output
    (mu Mb R buffer kappa : ℝ)
    (hmu : 0 < mu) (hMb : 0 < Mb) (hR : 0 < R) (hbuffer : 0 < buffer)
    (hkappa : 0 < kappa)
    (secondaryReserve : ℝ) (hSecondaryReserve : 0 < secondaryReserve)
    (SecondaryInverse SecondaryCutoff SecondaryObserver : ℕ → ℝ)
    (hSecondaryInverse : ∀ j, 0 ≤ SecondaryInverse j)
    (hSecondaryCutoff : ∀ j, 0 ≤ SecondaryCutoff j)
    (hSecondaryObserver : ∀ j, 0 ≤ SecondaryObserver j)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (kernel : RepairOriginalPrimaryKernelInputs Data (actualOriginalNativeOpen Data) kappa)
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
    (hFinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤)
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    let cT := (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2
    let BInv := fixedOriginalInverseBase mu Mb
    let HGrid := fixedOriginalGridRatio mu Mb buffer
    ∀ (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V)
      (hOne : EqOn psi 1 V)
      (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
      (hCompact : ∀ i, IsCompact (tsupport (theta i)))
      (hSupport : ∀ i, tsupport (theta i) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
      (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta)
      (hSecondaryMargin : ∀ r i (a : secondary.s r i), secondaryReserve ≤ (secondary.piece r i a).cT)
      (secondaryProfiles : ∀ ell, 0 ≤ ell → ell ≤ 1 →
        IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta secondary ell
          SecondaryInverse SecondaryCutoff SecondaryObserver)
      (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set (Ep × D))
      (hO : ∀ nu i, IsOpen (O nu i))
      (hONative : ∀ nu i, O nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i)
      (hRadius : ∀ nu i, originalNativePrimaryCarrier Data i nu
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R)
      (hBuffer : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) → ball x buffer ⊆ O nu i)
      (hNoncritical : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) →
        mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
          (ContinuousLinearMap.inr ℝ Ep D)‖)
      (hFirst : ∀ nu i x, x ∈ O nu i →
        ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
      (hSecond : ∀ nu i x, x ∈ O nu i →
        buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb),
    ∃ (budgeted : OriginalCountedPrimarySupply Data theta),
    0 < cT ∧ 0 < BInv ∧ 0 < HGrid ∧
    (∀ nu i, budgeted.mu nu i = mu) ∧
    (∀ nu i, budgeted.Mb nu i = Mb) ∧
    (∀ nu i, budgeted.buffer nu i = buffer) ∧
    (∀ nu i, budgeted.radius nu i = R) ∧
    (∀ nu i a, (budgeted.packet.piece nu i a).Bnative = 2*(1+2*Mb)) ∧
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
  intro theta cT BInv HGrid V hV hKV hOne hSmooth hCompact hSupport hPart hCount
    secondary hSecondaryMargin secondaryProfiles O hO hONative hRadius hBuffer hNoncritical hFirst hSecond
  obtain ⟨counted,hMuEq,hMbEq,hBufferEq,hRadiusEq,hBnative⟩ :=
    original_open_counted_primary_supply_from_common_geometry mu Mb R buffer hmu hMb.le hR hbuffer
      Data hd hs theta hCompact hSmooth hSupport O hO hONative hRadius hBuffer
      hNoncritical hFirst hSecond
  let budgeted := counted.toOriginalBudgetedPrimarySupply
  let primary := budgeted.packet
  have hInner (nu) (i) (a : primary.s nu i) (y : Ep × M)
      (hy : y ∈ tsupport (primary.piece nu i a).cutoff) :
      y.2 ∈ Data.atlas.inner (primary.piece nu i a).host := by
    have hyT := (primary.piece nu i a).source_domain ((primary.piece nu i a).support hy)
    have hPhysical := (round3ParameterSupportedPullback_tsupport_iff
      (round3ParameterProductChart (M := M) (Data.parameterChart i.2)).symm
      (theta i) y hyT).mp (primary.native_parent nu i a hy)
    rw [primary.host nu i a]
    exact (original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
      BS TS BP TP Ds Dp RS RP psi i hPhysical).2
  obtain ⟨geometry,hcT⟩ := original_budgeted_reference_profiles_from_kernel
    Data hd hs hp hImm theta budgeted hInner Mb kappa hMb.le hkappa
    (fun nu i => (hMbEq nu i).le) kernel
  let profiles := geometry.toRound3ParameterWholeReferenceProfiles
  have hBInv : 0 < BInv := fixedOriginalInverseBase_pos mu Mb
  have hHGrid : 0 < HGrid := fixedOriginalGridRatio_pos mu Mb buffer
  have hBase (nu) (i) :
      actualEuclideanPhaseInverseJetCost (budgeted.mu nu i) (budgeted.Mb nu i) 0 0 ≤ BInv := by
    change actualEuclideanPhaseInverseJetCost (counted.mu nu i) (counted.Mb nu i) 0 0 ≤ _
    rw [hMuEq nu i,hMbEq nu i]
    exact (le_abs_self _).trans (by dsimp [BInv,fixedOriginalInverseBase]; linarith)
  have hRatio (nu) (i) :
      actualPhaseRefinementFactor (budgeted.mu nu i) (budgeted.Mb nu i)/budgeted.buffer nu i ≤ HGrid := by
    change actualPhaseRefinementFactor (counted.mu nu i) (counted.Mb nu i)/counted.buffer nu i ≤ _
    rw [hMuEq nu i,hMbEq nu i,hBufferEq nu i]
    exact (le_abs_self _).trans (by dsimp [HGrid,fixedOriginalGridRatio]; linarith)
  have hCTEq : profiles.cT = cT := hcT
  have hcT' : 0 < cT := by
    rw [← hCTEq]
    exact profiles.cT_pos
  refine ⟨counted,hcT',hBInv,hHGrid,hMuEq,hMbEq,hBufferEq,hRadiusEq,hBnative,?_⟩
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
  rw [← hCTEq]
  rw [← hThreshold]
  exact prepared_current_common_secondary_finite_budget_output
    secondaryReserve hSecondaryReserve SecondaryInverse SecondaryCutoff SecondaryObserver
    hSecondaryInverse hSecondaryCutoff hSecondaryObserver Data hd hs hn hp hImm hLinear hDecomp
    rho hReserve c hEll Lactive hPrimaryCount Β (fun a => a.1.1)
    g hPreserves hTarget (fun _ => rfl) (fun _ => rfl) V hV hKV
    theta secondary hSecondaryMargin secondaryProfiles
    (fun i z hz => ⟨(hSupport i hz).1.1,mem_univ _⟩)
    hPart ((Ds+1)*(Dp+1)) hCount profiles.cT profiles.cT_pos
    Inverse Forward Meta hInverse hForward hMeta
    (((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D))
    q hq allowed hAllowed hFinite
    (fun ell hell hell1 hPrefix i => Classical.choice (hPrepared ell hell hell1 hPrefix i))


end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.localized_raw_common_geometry_secondary_budget_output
