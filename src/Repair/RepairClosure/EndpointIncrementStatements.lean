import OriginalIntegration.FinitePositiveFiniteEntranceStatement
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs
import FaithfulCollars.OriginalNormBufferGeometry
import Repair.EntranceOriginalObserverJets
import OriginalIncrements.CommonMeanNumerics
import OriginalIntegration.OriginalPrimaryInteraction
import OriginalIntegration.IncrementOutput
import OriginalCollars.ProtectedRegionPrimaryGeometry
import OriginalCollars.NativePrimitiveSignedRegion

/-!
# Independent proposition-valued original increment targets

These complete expressions originate in the previous independently written
source review, re-read against lem:increments in this continuation. They are
ordinary definitions without proof holes. No solution root is imported.
The raw numeric companion is kept separate from the fixed prescribed-data
producer, so their different orders of quantification remain visible.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.RepairClosure
open GlobalEmbedding.Continuation GlobalEmbedding.Continuation.OriginalIntegration
open GlobalEmbedding.Continuation.OriginalIncrements GlobalEmbedding.Continuation.FaithfulCollars
open GlobalEmbedding.Continuation.OriginalCollars GlobalEmbedding.Continuation.FaithfulIncrements
universe uM uP

/-- Unconditional fixed prescribed-data existence at every allowed scale.
The admissible finite budget is manufactured internally; no Given bound
is added to the source's fixed-data existence assertion. -/
def EndpointFixedIncrementTarget : Prop := ∀
    {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (RSrc bSrc RPar bPar : ℝ)
    (gS : OriginalSourceNormBuffer Data.atlas Data.sourceNormDomain RSrc bSrc)
    (WParam : Fin Data.parameterCount → Set P)
    (gP : OriginalParameterNormBuffer Data.parameterChart Data.parameterNormDomain
      WParam Data.parameterSet RPar bPar)
    (TS TP Parameter Spatial : ℕ → ℝ)
    (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (Ds Dp : ℕ) (hDs : Data.atlas.supportDegree ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree WParam i ≤ Dp)
    (hSTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.atlas.chart p).target,
      (Data.atlas.chart p).symm y ∈ Data.atlas.support i →
      ‖iteratedFDeriv ℝ j (Data.atlas.chart i ∘ (Data.atlas.chart p).symm) y‖ ≤ TS j)
    (hPTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.parameterChart p).target,
      (Data.parameterChart p).symm y ∈ WParam i →
      (Data.parameterChart p).symm y ∈ (Data.parameterChart i).source →
      ‖iteratedFDeriv ℝ j (Data.parameterChart i ∘ (Data.parameterChart p).symm) y‖ ≤ TP j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial),
    FinitePositiveIncrementsFixedData Data


/-- Independent original fixed-decomposition statement, including the actual
finite-prefix entrance, full original output and exact prefix invariance. -/
def EndpointSampledIncrementTarget : Prop := ∀
    {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (RSrc bSrc RPar bPar : ℝ)
    (gS : OriginalSourceNormBuffer Data.atlas Data.sourceNormDomain RSrc bSrc)
    (WParam : Fin Data.parameterCount → Set P)
    (gP : OriginalParameterNormBuffer Data.parameterChart Data.parameterNormDomain
      WParam Data.parameterSet RPar bPar)
    (TS TP Parameter Spatial : ℕ → ℝ)
    (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (Ds Dp : ℕ) (hDs : Data.atlas.supportDegree ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree WParam i ≤ Dp)
    (hSTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.atlas.chart p).target,
      (Data.atlas.chart p).symm y ∈ Data.atlas.support i →
      ‖iteratedFDeriv ℝ j (Data.atlas.chart i ∘ (Data.atlas.chart p).symm) y‖ ≤ TS j)
    (hPTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.parameterChart p).target,
      (Data.parameterChart p).symm y ∈ WParam i →
      (Data.parameterChart p).symm y ∈ (Data.parameterChart i).source →
      ‖iteratedFDeriv ℝ j (Data.parameterChart i ∘ (Data.parameterChart p).symm) y‖ ≤ TP j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial),
    ∃ (BS BP : ℕ → ℝ) (cT Mb BInv HGrid : ℝ),
      (∀ j, 0 ≤ BS j) ∧ (∀ j, 0 ≤ BP j) ∧
      0 < cT ∧ 0 < Mb ∧ 0 < BInv ∧ 0 < HGrid ∧
      ∀ (q : ℕ), 1 ≤ q → ∀ (allowed : ℕ → ℝ)
        (hAllowed : ∀ j, j ≤ (q+1)*(q+4)+2 → 0 ≤ allowed j),
      let J := (q+1)*(q+4)+2
      let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
      let Theta := commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
        q Rsub (originalPrimaryInteractionDegree Data+1) rho c cT Mb BInv HGrid hReserve.reserve_pos
        BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed
      FinitePositiveIncrementFiniteEntrance Data q J allowed Theta ∧
        ∀ (allowed' : ℕ → ℝ) (hAllowed' : ∀ j, j ≤ J → 0 ≤ allowed' j),
          (∀ j, j ≤ J → allowed j = allowed' j) →
          Theta = commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
            q Rsub (originalPrimaryInteractionDegree Data+1) rho c cT Mb BInv HGrid hReserve.reserve_pos
            BS TS BP TP Parameter Spatial allowed' Ds Dp hAllowed'

/-- Independent bounded chosen-phase numerical-class certificate. Its C precedes
all actual data, chart counts and construction high-order profiles. -/
def EndpointBoundedIncrementTarget : Prop := ∀
    {m d N : ℕ} {M : Type uM}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (mu Mb R buffer kappa : ℝ)
    (hmu : 0 < mu) (hMb : 0 < Mb) (hR : 0 < R)
    (hbuffer : 0 < buffer) (hkappa : 0 < kappa)
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
    (hAllowed : ∀ j, j ≤ (q+1)*(q+4)+2 → 0 ≤ allowed j)
    (hTailNonneg : ∀ j, 0 ≤ tail j),
    let cT := (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2
    let BInv := 1+|actualEuclideanPhaseInverseJetCost mu Mb 0 0|
    let HGrid := 1+|actualPhaseRefinementFactor mu Mb/(buffer/2)|
    let J := (q+1)*(q+4)+2
    let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
    let Theta := commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT Mb BInv HGrid hrho
      BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
    ∀ (P : Type uP) [TopologicalSpace P] [T2Space P]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P (EuclideanSpace ℝ (Fin d)))
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
      (hSmooth : ∀ i, ContMDiff
        ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
        𝓘(ℝ,ℝ) ∞ (theta i))
      (hCompact : ∀ i, IsCompact (tsupport (theta i)))
      (hParent : ∀ i, tsupport (theta i) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1)
      (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1)
      (hCount : ∀ z,
        (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
    (coordinateBound sLower nativeTwo : ℝ) (Phase : ℕ → ℝ)
    (hCoordinate : 0 ≤ coordinateBound) (hPhase : ∀ j, 0 ≤ Phase j)
    (hPhaseFirst : Phase 1 ≤ sMb) (hPhaseSecond : sBuffer*Phase 2 ≤ sMb)
    (hSLower : 0 < sLower) (hNativeTwo : 0 ≤ nativeTwo)
    (O : Fin Data.primaryCount → Fin Data.atlas.count × Fin Data.parameterCount →
      Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))))
    (hO : ∀ nu i, IsOpen (O nu i))
    (hNative : ∀ nu i, O nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i)
    (hRadius : ∀ nu i, originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆ closedBall 0 R)
    (hBuffer : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) → ball x buffer ⊆ O nu i)
    (hNoncritical : ∀ nu i x, x ∈ originalNativePrimaryCarrier Data i nu
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) →
      mu ≤ ‖(fderiv ℝ (originalNativePrimaryPhase Data nu i) x).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin d))
          (EuclideanSpace ℝ (Fin (m+1))))‖)
    (hFirst : ∀ nu i x, x ∈ O nu i →
      ‖fderiv ℝ (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (hSecond : ∀ nu i x, x ∈ O nu i →
      buffer*‖iteratedFDeriv ℝ 2 (originalNativePrimaryPhase Data nu i) x‖ ≤ Mb)
    (kernel : OriginalRegionPrimaryKernelInputs Data O kappa)
    (region : ∀ r i, NativePrimitiveSignedRegion Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      sMu sR sBuffer coordinateBound sKernel sLower nativeTwo Phase),
    ∀ ell, 0 < ell → ell ≤ 1 → OriginalFinitePrefixBudget Data J allowed ell →
    ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
      OriginalIncrementOutput Data q C ell tau delta


end GlobalEmbedding.Continuation.RepairClosure
