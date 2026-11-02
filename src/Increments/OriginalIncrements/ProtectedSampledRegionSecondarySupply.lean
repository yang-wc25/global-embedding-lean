import FaithfulIncrements.PreparedFiniteBudgetOutput
import OriginalCollars.SampledNativePrimitiveSecondaryPacket
import OriginalCollars.ProtectedRegionNativeSignedRegions
import OriginalIncrements.CarrierSampleSecondaryProfiles
import OriginalCollars.ProtectedRegionPrimaryGeometry
import OriginalIncrements.SampledSecondaryProfilesAtScale
import OriginalIncrements.SampledSecondaryNumericalProfiles

/-!
# The same protected secondary packet uses only sampled high jets

The compact parameter set may be proper. Only actual carrier points are
sampled in the original Omega/Q; no open construction region is required
to lie in K or in either norm domain. The same original signed phases,
map, target, cutoffs and support pairs are retained under protection.
Construction-neighborhood high jets are used to manufacture the packet;
the observer estimates below read only the actual original Given samples.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIncrements
open OriginalCollars FaithfulIncrements
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)

theorem protected_sampled_region_secondary_supply
    (primaryMu primaryMb primaryR primaryBuffer primaryKernel : ℝ)
    (mu Mb R buffer coordinateBound kernel lower nativeTwo : ℝ) (Phase : ℕ → ℝ)
    (hmu : 0 < mu) (hMb : 0 ≤ Mb) (hbuffer : 0 < buffer) (hPrimaryBuffer : 0 < primaryBuffer)
    (hCoordinate : 0 ≤ coordinateBound) (hPhase : ∀ j, 0 ≤ Phase j)
    (hFirstBudget : Phase 1 ≤ Mb) (hSecondBudget : buffer*Phase 2 ≤ Mb)
    (hKernel : 0 < kernel) (hLower : 0 < lower) (hNativeTwo : 0 ≤ nativeTwo)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (Parameter Spatial : ℕ → ℝ) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep) (hChart : B.chart=Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameterSample : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V) (hOne : EqOn psi 1 V)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hThetaExact : theta=fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i))
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (q : OriginalProtectedRegionPrimaryData Data theta primaryMu primaryMb primaryR primaryBuffer primaryKernel)
    (region : ∀ r i, NativePrimitiveSignedRegion Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      mu R buffer coordinateBound kernel lower nativeTwo Phase) :
    let L := localPrimaryData Data q.parameterOpen q.primaryDomain
    let hdL := q.domain_conditions hd
    let hsL := q.smooth_inputs hs
    let buffer' := min buffer (primaryBuffer/2)
    let reserve := sampledSecondaryReserve m Mb kernel
    ∃ packet : Round3PreparedParameterSecondaryPacket L hdL hsL theta,
      (∀ r i a, reserve ≤ (packet.piece r i a).cT) ∧
      (∀ (Packet : ℕ → ℝ) ell, 0 < ell → ell ≤ 1 →
        (∀ k, actualOriginalGivenInputProfile L k ell ≠ ⊤) →
        (∀ k, (actualOriginalGivenInputProfile L k ell).toReal ≤ Packet k) →
        IncrementsCompletionAtScaleSecondaryPacketProfiles L hdL hsL theta packet ell
          (phaseObserverInverseBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial)
          (incrementSecondaryCutoffProfile (Ep × D) mu Mb buffer' BS TS BP TP Ds Dp)
          (phaseObserverForwardBudget mu Mb (signedPhaseFromGivenBudget m d Packet) Parameter Spatial)) ∧
      (∀ r i, (packet.s r i).card ≤ countedSignedTotalRefinementBound («Ep» := Ep) (m := m)
        mu Mb R buffer' hmu hMb (lt_min hbuffer (half_pos hPrimaryBuffer))) ∧
      (∀ r i (a : packet.s r i),
        ((Data.parameterChart i.2).symm a.val.1,(Data.atlas.chart i.1).symm a.val.2) ∈
          tsupport (theta i) ∩ (tsupport (Data.cutoff r.val.1.1) ∩ tsupport (Data.cutoff r.val.1.2))) := by
  subst theta
  intro L hdL hsL buffer' reserve
  have hBuffer' : 0 < buffer' := lt_min hbuffer (half_pos hPrimaryBuffer)
  have hSecond' : buffer'*Phase 2 ≤ Mb :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (hPhase 2)).trans hSecondBudget
  have hTransitionL : RepairOriginalTransitionBudgets L Parameter Spatial :=
    ⟨transition.parameter,transition.spatial⟩
  obtain ⟨packet,numeric,hInv,hFirst,hTrans,hHessian,hCard,hCenters,hNumbers,hScalar,hParameterQ,hControls⟩ :=
    sampled_native_primitive_parameter_secondary_numerical_packet mu Mb R buffer' coordinateBound kernel lower nativeTwo Phase
      hmu hMb hBuffer' hCoordinate hPhase hFirstBudget hSecond' hKernel hLower hNativeTwo L hdL hsL
      _ hCompact hSmooth (fun i z hz => ⟨(q.parent_support i hz).1.1,(q.parent_support i hz).2⟩)
      (localized_parent_original_carrier_samples L B hChart BS TS BP TP Ds Dp RS RP
        hSource hParameterSample psi)
      (fun r i => q.protect_native_primitive_signed_region i r mu R buffer coordinateBound kernel lower nativeTwo Phase
        (region r i))
  refine ⟨packet,?_,?_,hCard,hCenters⟩
  · intro r i a
    rw [numeric.transverse_value,hTrans,sampledSecondaryReserve_eq]
  · intro Packet ell hell hellOne hFinite hGiven
    exact original_sampled_secondary_profiles_at_scale L hdL hsL mu Mb buffer' hmu hMb hBuffer'
      BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP hSource hParameterSample
      psi V hV hKV hOne packet hControls (fun r i a => (hNumbers r i a).2.2)
      (fun r i j a x => hScalar r i j buffer' hBuffer'.le le_rfl a x)
      Parameter Spatial Packet hParameter hSpatial hTransitionL ell hell hellOne hFinite hGiven

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.protected_sampled_region_secondary_supply
