import Probes.Round4LocalMeanPreparation
import Probes.Round3ParameterFixedCarrierMeanPreparation
import Probes.Round3ParameterAfterNormalFamily
import Probes.Round3ParameterActualHostRestriction
import Probes.Round3ParameterMeanPreparationOfFields
import Smoothing.Round3ParameterNativeRestriction
import Smoothing.Round3OuterParameterFixedCarrier

/-!
The actual fixed-carrier, after-normal factory with a local primary multiplicity.
The charts, restricted carriers, free normal, cutoffs, native samples and the
actual mean reserve construction are exactly the existing constructions.
Only the local support bound, derived independently from actual cutoffs,
replaces the coarse bound by the total number of primary labels.
-/

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

def Round4ParameterOriginalGeneratedMeanSupply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x)))
    {Sub : Type*} [Fintype Sub]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (ell c cT rho ML : ℝ) (q R Lprimary : ℕ)
    (Packet Forward Inverse Meta : ℕ → ℝ) : Prop :=
  let ForwardPrefix := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k)
    let MetaPrefix := fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S univ hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s B => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+ForwardPrefix (s+(q+4))) (MetaPrefix (s+(q+4))) B Inverse
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+ForwardPrefix (s+(q+4))) Inverse
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Inverse
    let Tfixed := parameterRound2_identityRawTransition m d Packet ForwardPrefix
    0 < radius ∧ ∀ K : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S univ,
      K.val = Data.H → Round3ParameterMeanRawReserveSupply (Tr := ℝ) Data.atlas Data.parameterChart
        S univ p K radius q R Lprimary (rho/4) Bnd Mg Dinput Tfixed
        (fun p x => Data.F (p,x)) hF g Data.primaryDomain ell

theorem round4Parameter_fixed_carrier_after_normal_mean_factory_local
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref)
    {Sub : Type*} [Fintype Sub]
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x)))
    (R Lprimary : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g0 R)
    (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
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
    Round4ParameterOriginalGeneratedMeanSupply Data hF g hS ell c cT rho ML q R Lprimary Packet Forward Inverse Meta := by
  intro domain Data gFixed hd hs hn hAll ell c cT hell hell1 host b e hdata hNative hInner hChart hInverse
    hTransverse hp hF hImm hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML q Packet hInverseNonneg hGiven hPacket
  obtain ⟨hActive,hGeometry,hProfilesNew,hEta,hChartSame,hInverseSame,hPrep⟩ :=
    round3Parameter_fixed_carrier_after_normal_mean_preparation Ref hdRef g0 R geom hOpen
      Forward Inverse Meta hProfiles F H normal neighborhood hd hs hn hAll ell cT hell.le hell1
      host b e hdata hNative hInner hChart hInverse hTransverse
  refine ⟨hActive,hGeometry,hProfilesNew,?_⟩
  exact round3Parameter_actual_closed_original_mean_raw_reserve_supply Data hd hs hn hp hAll hF
    (round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive)
    hImm ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML
    q R Lprimary Packet Inverse
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
    (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k)) hInverseNonneg
    (fun _ => round3PreparedFiniteMaximum_nonneg _) (fun _ => round3PreparedFiniteMaximum_nonneg _)
    hGiven hPacket (fun i => round4NativeMeanPreparationLocal Data hd hs hn
      (round3ParameterAfterNormalFamily Ref gFixed F H Ref.parameterOpen normal domain neighborhood hd hs hn hActive)
      ell cT Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k))
      R Data.primaryCount Lprimary i hLocal (Classical.choice (hPrep i)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_fixed_carrier_after_normal_mean_factory_local
