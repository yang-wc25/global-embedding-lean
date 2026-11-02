import OriginalIntegration.IncrementOutput
import OriginalIncrements.CommonSecondaryRawOutput
import OriginalCollars.ProtectedCommonGeometryPacket

/-!
# Common secondary bounds survive protected localization and the original exit

The actual signed packet belongs to the very protected datum used by the
mean construction. Its common reserve and profiles are consumed directly.
The same displacement is returned to the original datum, with unchanged
physical fields and original norm domains.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulIncrements FaithfulIntegration OriginalIncrements

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

theorem protected_common_secondary_increment
    (mu Mb R buffer kappa : ℝ) (hMb : 0 < Mb) (hkappa : 0 < kappa)
    (secondaryReserve : ℝ) (hSecondaryReserve : 0 < secondaryReserve)
    (SecondaryInverse SecondaryCutoff SecondaryObserver : ℕ → ℝ)
    (hSecondaryInverse : ∀ j, 0 ≤ SecondaryInverse j)
    (hSecondaryCutoff : ∀ j, 0 ≤ SecondaryCutoff j)
    (hSecondaryObserver : ∀ j, 0 ≤ SecondaryObserver j)
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
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V)
      (hOne : EqOn psi 1 V)
      (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
      (hCompact : ∀ i, IsCompact (tsupport (theta i)))
      (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (localization : OriginalProtectedCommonPrimaryData Data theta mu Mb R buffer kappa)
      (secondary : Round3PreparedParameterSecondaryPacket (localPrimaryData Data localization.parameterOpen localization.primaryDomain)
        (localization.domain_conditions hd) (localization.smooth_inputs hs) theta)
      (hSecondaryMargin : ∀ r i (a : secondary.s r i), secondaryReserve ≤ (secondary.piece r i a).cT)
      (secondaryProfiles : ∀ ell, 0 ≤ ell → ell ≤ 1 →
        IncrementsCompletionAtScaleSecondaryPacketProfiles (localPrimaryData Data localization.parameterOpen localization.primaryDomain)
          (localization.domain_conditions hd) (localization.smooth_inputs hs) theta secondary ell
          SecondaryInverse SecondaryCutoff SecondaryObserver),
    let cT := (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2
    let BInv := fixedOriginalInverseBase mu Mb
    let HGrid := fixedOriginalGridRatio mu Mb (buffer/2)
    ∀ (q : ℕ), 1 ≤ q → ∀ (allowed : ℕ → ℝ)
      (hAllowed : ∀ j, j ≤ (q+1)*(q+4)+2 → 0 ≤ allowed j),
    let J := (q+1)*(q+4)+2
    let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)
    let Theta := commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb BInv HGrid hReserve.reserve_pos
      BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ ell, 0 < ell → ell ≤ 1 → OriginalFinitePrefixBudget Data J allowed ell →
      ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
        OriginalIncrementOutput Data q C ell tau delta := by
  intro theta V hV hKV hOne hSmooth hCompact hPart hCount localization
    secondary hSecondaryMargin secondaryProfiles cT BInv HGrid
  let Vlocal := localization.parameterOpen
  let domain := localization.primaryDomain
  let L := localPrimaryData Data Vlocal domain
  have hVold : Vlocal ⊆ Data.parameterOpen := subset_closure.trans localization.parameter_closure
  have hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu :=
    fun nu z hz => (localization.primary_closure nu (subset_closure hz)).1
  let hdL := localization.domain_conditions hd
  let hsL := localization.smooth_inputs hs
  let hpL := localPrimaryData_phase_conditions Data hd hs hp Vlocal domain hVold hDomain hdL hsL
  let hnL := localPrimaryData_free_normal_conditions Data hd hs hn Vlocal domain hVold hDomain hdL hsL
  let hImmL := localPrimaryData_slice_immersion Data hImm Vlocal domain hVold
  let hLinearL := localPrimaryData_linear_smooth Data hLinear Vlocal domain hVold hDomain
  let hDecompL := localPrimaryData_decomposition Data hDecomp Vlocal domain hVold
  let hReserveL := localPrimaryData_reserve Data rho hReserve Vlocal domain hVold
  let hEllL := localPrimaryData_ellipticity Data c hEll Vlocal domain
  have hTransitionL : RepairOriginalTransitionBudgets L Parameter Spatial :=
    ⟨transition.parameter,transition.spatial⟩
  have hPrimaryCountL (z : P × M) (hz : z ∈ L.parameterSet ×ˢ (univ : Set M)) :
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport L nu)).card ≤ Lactive := by
    apply (Finset.card_le_card ?_).trans (hPrimaryCount z hz)
    intro nu hnu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact localPrimaryData_relative_support_subset Data Vlocal domain hVold nu
      (Finset.mem_filter.mp hnu).2
  let W := V ∩ Vlocal
  have hW : IsOpen W := hV.inter localization.parameter_open
  have hKW : Data.parameterSet ⊆ W := fun p hp => ⟨hKV hp,localization.parameter_sample hp⟩
  let g := localization.geometry
  obtain ⟨supply,hcT,hBInv,hHGrid,hMuEq,hMbEq,hBufferEq,hRadiusEq,hBnative,hOutput⟩ :=
    localized_raw_common_geometry_secondary_budget_output mu Mb R (buffer/2) kappa
      g.mu_pos hMb g.radius_pos g.buffer_pos hkappa
      secondaryReserve hSecondaryReserve SecondaryInverse SecondaryCutoff SecondaryObserver
      hSecondaryInverse hSecondaryCutoff hSecondaryObserver L hdL hsL hpL localization.kernel hnL
      hImmL hLinearL hDecompL rho hReserveL c hEllL BS TS BP TP hBS hTS hBP hTP Ds Dp
      B hChart RS RP hSource hParameter Parameter Spatial hParameterNonneg hSpatialNonneg
      hTransitionL Lactive hPrimaryCountL (fun j => localization.given_finite j 1)
      psi W hW hKW (fun p hp => hOne hp.1) hSmooth hCompact localization.parent_support
      (fun z hz => hPart z hz.1) hCount secondary hSecondaryMargin secondaryProfiles g.region g.open_region g.native g.radius g.buffered
      g.noncritical g.first g.second
  intro q hq allowed hAllowed
  obtain ⟨hTheta,hThetaOne,C,hC,hOutputAt⟩ := hOutput q hq allowed hAllowed
  refine ⟨hTheta,hThetaOne,C,hC,?_⟩
  intro ell hell hellOne hGiven tau delta hdelta hdeltaTau htauEll hRatio
  have hGivenL := localPrimaryData_original_budget Data Vlocal domain hd.primary_open
    localization.primary_open hDomain ((q+1)*(q+4)+2) allowed ell hGiven
  have hout : OriginalIncrementOutput L q C ell tau delta :=
    hOutputAt ell hell hellOne (fun j hj => (hGivenL j hj).2)
      tau delta hdelta hdeltaTau htauEll hRatio
  exact localPrimaryData_original_output Data Vlocal domain hVold q C ell tau delta hout

end GlobalEmbedding.Continuation.OriginalIntegration
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.protected_common_secondary_increment
