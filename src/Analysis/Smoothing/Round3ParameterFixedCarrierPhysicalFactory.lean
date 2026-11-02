import Smoothing.Round3ParameterFixedCarrierCanonicalFactory
import Probes.Round3ParameterPreparedPhysicalGeometry
import Smoothing.Round3ParameterClosedCanonicalRawSupply
import Smoothing.Round3ParameterFixedCarrierMeanFactory
import Probes.Round3ParameterFixedCarrierMeanPreparation
import Probes.Round3ParameterAfterNormalFamily
import Probes.Round3ParameterActualHostRestriction
import Probes.Round3ParameterMeanPreparationOfFields
import Smoothing.Round3ParameterNativeRestriction
import Smoothing.Round3OuterParameterFixedCarrier

/-! The actual normal stage feeds the same fixed-carrier mean family.
The native host charts are genuinely restricted and their phase-adapted
slices reconstructed. All forward and inverse functions stay unchanged.
No new cutoff, current-map profile maximum, or parameter shrink is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal TensorProduct
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance meanPrimitiveSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance meanPrimitiveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private local instance meanPrimitiveGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance meanPrimitiveGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance meanPrimitiveGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance meanPrimitiveGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance meanPrimitiveGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance meanPrimitiveGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance
private local instance meanPrimitiveGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanPrimitiveCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanPrimitiveCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace



private local instance finiteArgumentLinearNormed : NormedAddCommGroup ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance finiteArgumentLinearSpace : NormedSpace ℝ ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance finiteArgumentBilinearNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

theorem round3Parameter_fixed_carrier_after_normal_physical_factory
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref)
    {Sub : Type*} [Fintype Sub]
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g0 R)
    (hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g0.eta nu)))
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Ref
      (round3ParameterFixedCarrierFamily Ref g0 hOpen) Forward Inverse Meta)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (normal : Fin Ref.primaryCount → P × M → Ey)
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}) :
    let domain := fun nu => round3FixedCarrierDomain (g0.eta nu)
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen normal domain neighborhood
    let gFixed := round3ParameterFixedCarrierFamily Ref g0 hOpen
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) (hAll : Data.parameterSet = univ)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (host : Fin Ref.primaryCount → Fin Ref.parameterCount → Sub → Fin Ref.atlas.count)
    (b : Fin Ref.primaryCount → Fin Ref.parameterCount → Sub → OpenPartialHomeomorph X X)
    (e : Fin Ref.primaryCount → Fin Ref.parameterCount → Sub → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu ip a, ActualOriginalHostSliceData (Ref.atlas.chart (host nu ip a)) (b nu ip a)
      (fun z : Ep × M => Ref.phase nu ((Ref.parameterChart ip).symm z.1,z.2)) (e nu ip a))
    (hNative : ∀ nu ip a, (b nu ip a).source ⊆ actualOriginalNativeOpen Data (host nu ip a,ip))
    (hInner : ∀ nu ip a w, w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a)).source →
      w.2 ∈ Ref.atlas.inner (host nu ip a))
    (hChart : ∀ nu ip a, actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a) =
      (round3ParameterNativePrimary (fun p x => Ref.F (p,x)) g0 (Ref.parameterChart ip)).chart nu a)
    (hInverse : ∀ nu ip a p x, (e nu ip a p).symm x = g0.inverse nu a ((Ref.parameterChart ip).symm p) x)
    (hTransverse : ∀ (i : Fin Ref.atlas.count × Fin Ref.parameterCount) nu a z,
      z ∈ (b nu i.2 a).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (e nu i.2 a z.1).symm z.2 v‖^2),
    ∀ (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (ML : ℝ) (hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML)
    (q : ℕ) (Packet : ℕ → ℝ) (hInverseNonneg : ∀ k, 0 ≤ Inverse k)
    (hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n),
    ∃ hActive : ∀ nu a z, z ∈ (gFixed.chart nu a).target →
      (z.1,gFixed.inverse nu a z.1 z.2) ∈ domain nu ∩ incrementsOriginalParameterRegion Data,
    let g := round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive
    Round3ParameterOriginalPrimaryGeometry Data g R ∧
    Round3ParameterOriginalChartProfiles Data g Forward Inverse Meta ∧
    Round3ParameterOriginalGeneratedCanonicalSupply Data hF g hS ell c cT rho ML q R Packet Forward Inverse Meta ∧
    (∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
      Nonempty (ActualOriginalPrimaryPhysicalGeometry
        (fun p x => Data.F ((Data.parameterChart i.2).symm p,x))
        (fun p => hF ((Data.parameterChart i.2).symm p))
        (round3ParameterNativePrimary (fun p x => Data.F (p,x))
          (round3Parameter_restrictPrimaryFamily (fun p x => Data.F (p,x)) g univ isOpen_univ)
          (Data.parameterChart i.2)))) := by
  intro domain Data gFixed hd hs hn hAll ell c cT hell hell1 host b e hdata hNative hInner hChart hInverse
    hTransverse hp hF hImm hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML q Packet hInverseNonneg hGiven hPacket
  obtain ⟨hActive,hGeometry,hProfilesNew,hEta,hChartSame,hInverseSame,hPrep⟩ :=
    round3Parameter_fixed_carrier_after_normal_mean_preparation Ref hdRef g0 R geom hOpen
      Forward Inverse Meta hProfiles F H normal neighborhood hd hs hn hAll ell cT hell.le hell1
      host b e hdata hNative hInner hChart hInverse hTransverse
  refine ⟨hActive,hGeometry,hProfilesNew,?_,?_⟩
  · exact round3Parameter_actual_closed_original_canonical_raw_reserve_supply Data hd hs hn hp hAll hF
      (round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive)
      hImm ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML
      q R Data.primaryCount Packet Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) hInverseNonneg
      (fun _ => round3PreparedFiniteMaximum_nonneg _) (fun _ => round3PreparedFiniteMaximum_nonneg _)
      hGiven hPacket (fun i => Classical.choice (hPrep i))
  · intro i
    exact round3Parameter_prepared_native_physical_geometry Data hd hs hn hAll hF
      (round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive)
      hImm ell cT hcT Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) R Data.primaryCount i
      (Classical.choice (hPrep i))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_fixed_carrier_after_normal_physical_factory
