import OriginalIntegration.BoundedSampledRegionPrimitivePhaseIncrement
import OriginalCollars.OriginalCommonPrimitiveExistence
import OriginalCollars.OriginalCommonPrimaryExistence
import CompletionIntegration.ManufacturedLocalSupply

/-!
# The actual original phase family supplies both common refinements

All low geometric numbers are manufactured from the literal fixed data
before q and the finite input prefix. Both primary and signed-secondary
regions come from the original Good conditions on actual compact carriers.
Higher observer profiles use the unchanged original Given samples. This
fixed-data realization is paired with the preceding bounded-class theorem;
it does not substitute compactness for class-uniform geometric margins.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion OriginalCollars FaithfulIncrements OriginalIntegration
universe uM uP
variable {m d N : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

theorem actual_sampled_common_raw_output
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
    ∃ cT Mb BInv HGrid : ℝ,
      0 < cT ∧ 0 < Mb ∧ 0 < BInv ∧ 0 < HGrid ∧
      ∀ (q : ℕ), 1 ≤ q → ∀ (allowed : ℕ → ℝ)
        (hAllowed : ∀ k, k ≤ (q+1)*(q+4)+2 → 0 ≤ allowed k),
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
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  obtain ⟨psi,V,hV,hKV,hVU,hPsi,hOne,hPsiSupport,hRange,hSmooth,hCompact,hSub,hSupport,hPart,hCount,hGerm⟩ :=
    completion_original_parameter_localized_parents BS TS BP TP hBS hTS hBP hTP Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet Data.parameterOpen
      hd.parameter_compact hd.parameter_open hd.parameter_subset RS RP
  let theta := fun i => sourceCollarNovParameterLocalized psi
    (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i)
  have hSupport' : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1 := by
    simpa only [hChart] using hSupport
  obtain ⟨mu,Mb,R,buffer,kappa,hmu,hMb,hR,hbuffer,hkappa,geometry,kernel⟩ :=
    original_common_primary_geometry_exists Data hd hs hp hImm theta hCompact hSmooth hSupport'
  obtain ⟨sMu,sMb,sR,sBuffer,coordinateBound,sKernel,sLower,nativeTwo,Phase,
      hSMu,hSMb,hSR,hSBuffer,hCoordinate,hSKernel,hSLower,hNativeTwo,hPhase,hPhaseFirst,hPhaseSecond,regions⟩ :=
    original_common_native_primitive_regions_exist Data hd hs hp hImm theta hCompact hSmooth hSupport'
  let cT := (kappa/((2*(1+2*Mb))^2*actualIncrementSortedSymmetricConstant m))^2
  let BInv := fixedOriginalInverseBase mu Mb
  let HGrid := fixedOriginalGridRatio mu Mb (buffer/2)
  have hcT : 0 < cT := by
    exact sq_pos_of_pos (div_pos hkappa (mul_pos
      (sq_pos_of_pos (by positivity : 0 < 2*(1+2*Mb)))
      (actualIncrementSortedSymmetricConstant_pos m)))
  refine ⟨cT,Mb,BInv,HGrid,hcT,hMb,fixedOriginalInverseBase_pos mu Mb,
    fixedOriginalGridRatio_pos mu Mb (buffer/2),?_⟩
  intro q hq allowed hAllowed
  let tail := fun j => (actualOriginalGivenInputProfile Data j 1).toReal
  have hTailNonneg : ∀ j, 0 ≤ tail j := fun j => ENNReal.toReal_nonneg
  obtain ⟨hTheta,hThetaOne,C,hC,hRun⟩ :=
    bounded_sampled_region_primitive_phase_increment.{uM,uP} (m := m) (d := d) (N := N) (M := M)
      mu Mb R buffer kappa hmu hMb hR hbuffer hkappa
      sMu sMb sR sBuffer sKernel hSMu hSMb.le hSBuffer hSKernel
      rho hReserve.reserve_pos c BS TS BP TP hBS hTS hBP hTP Ds Dp
      Parameter Spatial hParameterNonneg hSpatialNonneg Lactive q hq allowed tail hAllowed hTailNonneg
  refine ⟨hTheta,hThetaOne,C,hC,?_⟩
  exact hRun P Data hd hs hp hn hImm hLinear hDecomp hReserve hEll B hChart RS RP
    hSource hParameter transition hPrimaryCount
    (fun j _ => (ENNReal.ofReal_toReal (hFinite j)).symm.le)
    psi theta rfl V hV hKV hOne hSmooth hCompact hSupport' hPart hCount
    coordinateBound sLower nativeTwo Phase hCoordinate.le hPhase hPhaseFirst hPhaseSecond hSLower hNativeTwo
    geometry.region geometry.open_region geometry.native geometry.radius geometry.buffered
    geometry.noncritical geometry.first geometry.second kernel (fun r i => Classical.choice (regions r i))

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.actual_sampled_common_raw_output
