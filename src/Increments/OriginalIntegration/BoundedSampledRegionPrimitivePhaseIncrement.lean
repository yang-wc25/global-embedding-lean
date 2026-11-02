import OriginalIntegration.BoundedSampledProtectedRegionKernelIncrement
import OriginalIncrements.ProtectedSampledRegionSecondarySupply
import OriginalIncrements.PrimitivePrimaryProtectedRegionData

/-!
# Original sampled input bounds control the chosen-phase bounded class

Only original phase domains, jets and actual restricted operators enter.
The primary protected datum and both counted packets are manufactured.
The same original K, Omega/Q, F, H, phases and supports remain literal.
C is fixed before all actual data and both refinements. Positive secondary
jets are bounded at the unchanged original Given samples. The auxiliary
all-order phase profile on a construction neighborhood is selected after
Data and does not enter C. The high bounded input tail never enters the
finite scale threshold.

The original chosen-phase quantitative margins are imposed only on the
explicit construction neighborhoods O. No lower bound is required on the
rest of an old primary domain. Bounds only on K are not silently extended
to a common open neighborhood.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulIncrements FaithfulIntegration OriginalIncrements OriginalCollars

universe uM uP
variable {m d N : ℕ} {M : Type uM}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

theorem bounded_sampled_region_primitive_phase_increment
    (mu Mb R buffer kappa : ℝ)
    (hmu : 0 < mu) (hMb : 0 < Mb) (hR : 0 < R) (hbuffer : 0 < buffer) (hkappa : 0 < kappa)
    (sMu sMb sR sBuffer sKernel : ℝ)
    (hSMu : 0 < sMu) (hSMb : 0 ≤ sMb) (hSBuffer : 0 < sBuffer)
    (hSKernel : 0 < sKernel)
    (rho : ℝ) (hrho : 0 < rho) (c : ℝ)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (Lactive : ℕ) (q : ℕ) (hq : 1 ≤ q) (allowed tail : ℕ → ℝ)
    (hAllowed : ∀ j, j ≤ (q+1)*(q+4)+2 → 0 ≤ allowed j) (hTailNonneg : ∀ j, 0 ≤ tail j) :
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
      (hParent : ∀ i, tsupport (theta i) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
      (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
    (coordinateBound sLower nativeTwo : ℝ) (Phase : ℕ → ℝ)
    (hCoordinate : 0 ≤ coordinateBound) (hPhase : ∀ j, 0 ≤ Phase j)
    (hPhaseFirst : Phase 1 ≤ sMb) (hPhaseSecond : sBuffer*Phase 2 ≤ sMb)
    (hSLower : 0 < sLower) (hNativeTwo : 0 ≤ nativeTwo)
    (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount → Set (Ep × D))
    (hO : ∀ nu i, IsOpen (O nu i))
    (hNative : ∀ nu i, O nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (hRadius : ∀ nu i, originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R)
    (hBuffer : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) → ball x buffer ⊆ O nu i)
    (hNoncritical : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) →
      mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
        (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hFirst : ∀ nu i x, x ∈ O nu i → ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (hSecond : ∀ nu i x, x ∈ O nu i →
      buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (kernel : OriginalRegionPrimaryKernelInputs Data O kappa)
    (region : ∀ r i, NativePrimitiveSignedRegion Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      sMu sR sBuffer coordinateBound sKernel sLower nativeTwo Phase),
    ∀ ell, 0 < ell → ell ≤ 1 → OriginalFinitePrefixBudget Data J allowed ell →
    ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
      OriginalIncrementOutput Data q C ell tau delta := by
  intro cT BInv HGrid J Rsub Theta
  let sBuffer' := min sBuffer (buffer/2)
  have hSBuffer' : 0 < sBuffer' := lt_min hSBuffer (half_pos hbuffer)
  let Packet := boundedGivenEnvelope J allowed tail
  let secondaryReserve := sampledSecondaryReserve m sMb sKernel
  have hSecondaryReserve : 0 < secondaryReserve := sampledSecondaryReserve_pos m sMb sKernel hSMb hSKernel
  let SecondaryInverse := phaseObserverInverseBudget sMu sMb
    (signedPhaseFromGivenBudget m d Packet) Parameter Spatial
  let SecondaryObserver := phaseObserverForwardBudget sMu sMb
    (signedPhaseFromGivenBudget m d Packet) Parameter Spatial
  let SecondaryCutoff := incrementSecondaryCutoffProfile (Ep × D) sMu sMb sBuffer' BS TS BP TP Ds Dp
  have hProfileNonneg := sampled_secondary_profiles_nonneg m d sMu sMb hSMu hSMb
    Packet Parameter Spatial hParameter hSpatial
  have hObserver : ∀ j, 0 ≤ SecondaryObserver j := hProfileNonneg.1
  have hObsInverse : ∀ j, 0 ≤ SecondaryInverse j := hProfileNonneg.2
  have hCutoff : ∀ j, 0 ≤ SecondaryCutoff j := fun j =>
    incrementSecondaryCutoffProfile_nonneg _ sMu sMb sBuffer' BS TS BP TP Ds Dp j
      hSMu hSMb hSBuffer' hBS hTS hBP hTP
  obtain ⟨hTheta,hThetaOne,C,hC,hRaw⟩ :=
    bounded_sampled_protected_region_kernel_increment.{uM,uP} (m := m) (d := d) (N := N) (M := M)
      mu Mb R buffer kappa hmu hMb hR hbuffer hkappa secondaryReserve hSecondaryReserve
      SecondaryInverse SecondaryCutoff SecondaryObserver hObsInverse hCutoff hObserver
      rho hrho c BS TS BP TP hBS hTS hBP hTP Ds Dp Parameter Spatial hParameter hSpatial
      Lactive q hq allowed tail hAllowed hTailNonneg
  refine ⟨hTheta,hThetaOne,C,hC,?_⟩
  intro P _ _ _ _ Data hd hs hp hn hImm hLinear hDecomp hReserve hEll B hChart RS RP
    hSource hParameterSample transition hPrimaryCount hTail
    psi theta hThetaExact V hV hKV hOne hSmooth hCompact hParent hPart hCount
    coordinateBound sLower nativeTwo Phase hCoordinate hPhase hPhaseFirst hPhaseSecond hSLower hNativeTwo
    O hO hNative hRadius hBuffer hNoncritical hFirst hSecond kernel region
  obtain ⟨localization⟩ := primitive_primary_protected_region_data mu Mb R buffer kappa hmu hMb.le hR hbuffer
    Data hd hs hLinear Parameter Spatial hParameter hSpatial transition theta hCompact hSmooth hParent
    O hO hNative hRadius hBuffer hNoncritical hFirst hSecond kernel
  obtain ⟨secondary,hMargin,hProfiles,hCard,hCenters⟩ :=
    protected_sampled_region_secondary_supply mu Mb R buffer kappa
      sMu sMb sR sBuffer coordinateBound sKernel sLower nativeTwo Phase
      hSMu hSMb hSBuffer hbuffer hCoordinate hPhase hPhaseFirst hPhaseSecond hSKernel hSLower hNativeTwo
      BS TS BP TP hBS hTS hBP hTP Ds Dp Parameter Spatial hParameter hSpatial
      Data hd hs transition B hChart RS RP hSource hParameterSample
      psi V hV hKV hOne theta hThetaExact hCompact hSmooth localization region
  obtain ⟨primary,hMuEq,hMbEq,hBufferEq,hRadiusEq,hBnative,hOutput⟩ :=
    hRaw P Data hd hs hp hn hImm hLinear hDecomp hReserve hEll
      B hChart RS RP hSource hParameterSample transition hPrimaryCount hTail
      psi theta hThetaExact V hV hKV hOne hSmooth hCompact hPart hCount
      localization secondary hMargin (hProfiles Packet)
  exact hOutput

end GlobalEmbedding.Continuation.OriginalIntegration
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.bounded_sampled_region_primitive_phase_increment
