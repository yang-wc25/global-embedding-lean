import OriginalIntegration.ProtectedCommonSecondaryIncrement
import OriginalIncrements.BoundedSampledRegionKernelRawOutput

/-!
# Sampled secondary C(j) survives protected localization

The numerical bounded-input class fixes C before the parameter manifold
and original datum. The original high-input bounds are transported into
the internally finite protected domains by genuine extended-norm
monotonicity. No original all-order finiteness premise is needed. The
same actual primary packet is returned, and the same C, G and U give the
literal original estimates with the original Omega/Q and supports.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulIncrements FaithfulIntegration OriginalIncrements

universe uM uP
variable {m d N : ℕ} {M : Type uM}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

theorem bounded_sampled_protected_region_kernel_increment
    (mu Mb R buffer kappa : ℝ)
    (hmu : 0 < mu) (hMb : 0 < Mb) (hR : 0 < R) (hbuffer : 0 < buffer)
    (hkappa : 0 < kappa)
    (secondaryReserve : ℝ) (hSecondaryReserve : 0 < secondaryReserve)
    (SecondaryInverse SecondaryCutoff SecondaryObserver : ℕ → ℝ)
    (hSecondaryInverse : ∀ j, 0 ≤ SecondaryInverse j)
    (hSecondaryCutoff : ∀ j, 0 ≤ SecondaryCutoff j)
    (hSecondaryObserver : ∀ j, 0 ≤ SecondaryObserver j)
    (rho : ℝ) (hrho : 0 < rho) (c : ℝ)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (Parameter Spatial : ℕ → ℝ)
    (hParameterNonneg : ∀ k, 0 ≤ Parameter k) (hSpatialNonneg : ∀ k, 0 ≤ Spatial k)
    (Lactive : ℕ) (q : ℕ) (hq : 1 ≤ q) (allowed tail : ℕ → ℝ)
    (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k)
    (hTailNonneg : ∀ k, 0 ≤ tail k) :
    let cT := (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2
    let BInv := fixedOriginalInverseBase mu Mb
    let HGrid := fixedOriginalGridRatio mu Mb (buffer/2)
    let J := (q+1)*(q+4)+2
    let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)
    let Theta := commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb BInv HGrid hrho
      BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ (P : Type uP) [TopologicalSpace P] [T2Space P]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (hPrimaryCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu =>
        z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive)
    (hTail : ∀ k, J < k → actualOriginalGivenInputProfile Data k 1 ≤ ENNReal.ofReal (tail k))
    (psi : P → ℝ)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hThetaExact : theta = fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)),
    ∀ (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V)
      (hOne : EqOn psi 1 V)
      (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
      (hCompact : ∀ i, IsCompact (tsupport (theta i)))
      (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (localization : OriginalProtectedRegionPrimaryData Data theta mu Mb R buffer kappa)
      (secondary : Round3PreparedParameterSecondaryPacket (localPrimaryData Data localization.parameterOpen localization.primaryDomain)
        (localization.domain_conditions hd) (localization.smooth_inputs hs) theta)
      (hSecondaryMargin : ∀ r i (a : secondary.s r i), secondaryReserve ≤ (secondary.piece r i a).cT)
      (secondaryProfiles : ∀ ell, 0 < ell → ell ≤ 1 →
        (∀ k, actualOriginalGivenInputProfile
          (localPrimaryData Data localization.parameterOpen localization.primaryDomain) k ell ≠ ⊤) →
        (∀ k, (actualOriginalGivenInputProfile
          (localPrimaryData Data localization.parameterOpen localization.primaryDomain) k ell).toReal ≤
          boundedGivenEnvelope ((q+1)*(q+4)+2) allowed tail k) →
        IncrementsCompletionAtScaleSecondaryPacketProfiles (localPrimaryData Data localization.parameterOpen localization.primaryDomain)
          (localization.domain_conditions hd) (localization.smooth_inputs hs) theta secondary ell
          SecondaryInverse SecondaryCutoff SecondaryObserver),
    ∃ supply : OriginalCountedPrimarySupply
        (localPrimaryData Data localization.parameterOpen localization.primaryDomain) theta,
      (∀ nu i, supply.mu nu i = mu) ∧
      (∀ nu i, supply.Mb nu i = Mb) ∧
      (∀ nu i, supply.buffer nu i = buffer/2) ∧
      (∀ nu i, supply.radius nu i = R) ∧
      (∀ nu i a, (supply.packet.piece nu i a).Bnative = 2*(1+2*Mb)) ∧
      ∀ ell, 0 < ell → ell ≤ 1 → OriginalFinitePrefixBudget Data J allowed ell →
      ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
        OriginalIncrementOutput Data q C ell tau delta := by
  intro cT BInv HGrid J Rsub Theta
  obtain ⟨hTheta,hTheta1,C,hC,hRaw⟩ :=
    bounded_raw_sampled_region_kernel_secondary_output.{uM,uP} (m := m) (d := d) (N := N) (M := M)
      mu Mb R (buffer/2) kappa hmu hMb hR (half_pos hbuffer) hkappa
      secondaryReserve hSecondaryReserve SecondaryInverse SecondaryCutoff SecondaryObserver
      hSecondaryInverse hSecondaryCutoff hSecondaryObserver rho hrho c
      BS TS BP TP hBS hTS hBP hTP Ds Dp Parameter Spatial hParameterNonneg hSpatialNonneg
      Lactive q hq allowed tail hAllowed hTailNonneg
  refine ⟨hTheta,hTheta1,C,hC,?_⟩
  intro P _ _ _ _ Data hd hs hp hn hImm hLinear hDecomp hReserve hEll
    B hChart RS RP hSource hParameter transition hPrimaryCount hTail psi
    theta hThetaExact V hV hKV hOne hSmooth hCompact hPart hCount localization
    secondary hSecondaryMargin secondaryProfiles
  subst theta
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
  have hTailL (k : ℕ) (hk : J < k) :
      (actualOriginalGivenInputProfile L k 1).toReal ≤ tail k := by
    have hBound : actualOriginalGivenInputProfile L k 1 ≤ ENNReal.ofReal (tail k) :=
      (localPrimaryData_given_profile_le Data Vlocal domain hd.primary_open
        localization.primary_open hDomain k 1).trans (hTail k hk)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound).trans
      (by rw [ENNReal.toReal_ofReal (hTailNonneg k)])
  have hSecondaryAtScale (ell : ℝ) (hell : 0 < ell) (hellOne : ell ≤ 1)
      (hPrefix : ∀ k, k ≤ J → (actualOriginalGivenInputProfile L k ell).toReal ≤ allowed k) :
      IncrementsCompletionAtScaleSecondaryPacketProfiles L hdL hsL _ secondary ell
        SecondaryInverse SecondaryCutoff SecondaryObserver := by
    have hGiven := boundedGivenEnvelope_current_scale L J allowed tail
      (fun k => localization.given_finite k 1) hTailL ell hellOne hPrefix
    exact secondaryProfiles ell hell hellOne (fun k => (hGiven k).1) (fun k => (hGiven k).2)
  obtain ⟨supply,hcT,hBInv,hHGrid,hMuEq,hMbEq,hBufferEq,hRadiusEq,hBnative,hOutput⟩ :=
    hRaw P L hdL hsL hpL hnL hImmL hLinearL hDecompL hReserveL hEllL
      B hChart RS RP hSource hParameter hTransitionL hPrimaryCountL
      (fun j => localization.given_finite j 1) hTailL
      psi W hW hKW (fun p hp => hOne hp.1) hSmooth hCompact localization.parent_support
      (fun z hz => hPart z hz.1) hCount secondary hSecondaryMargin hSecondaryAtScale
      g.region g.open_region g.native g.radius g.buffered g.noncritical g.first g.second localization.kernel
  refine ⟨supply,hMuEq,hMbEq,hBufferEq,hRadiusEq,hBnative,?_⟩
  intro ell hell hellOne hGiven tau delta hdelta hdeltaTau htauEll hRatio
  have hGivenL := localPrimaryData_original_budget Data Vlocal domain hd.primary_open
    localization.primary_open hDomain J allowed ell hGiven
  have hout : OriginalIncrementOutput L q C ell tau delta :=
    hOutput ell hell hellOne (fun j hj => (hGivenL j hj).2)
      tau delta hdelta hdeltaTau htauEll hRatio
  exact localPrimaryData_original_output Data Vlocal domain hVold q C ell tau delta hout

end GlobalEmbedding.Continuation.OriginalIntegration
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.bounded_sampled_protected_region_kernel_increment
