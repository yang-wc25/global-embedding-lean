import Smoothing.Round3ParameterCanonicalMeanReserveSupply
import Smoothing.Round3ParameterOriginalCanonicalMeanAtlas
import Probes.Round3ParameterOriginalMeanPreparation
import Probes.Round3ParameterOriginalActiveRawProfiles
import Probes.Round3ParameterOriginalActiveMeanPrimitives
import Smoothing.Round3ParameterOriginalClosedMeanAtlas
import Smoothing.Round3ParameterMeanReserveSupply
import Smoothing.ParameterRound2OriginalGermReserveBall
import Smoothing.ParameterRound2IdentityRefinementSamples
import Smoothing.ParameterRound2IdentityRawCosts
/-! Original C0 closeness constructs a common genuine positive neighborhood
for a finite list of actual native tensors. The same actual original primary
family, restricted to this one neighborhood, then supplies every mean
primitive for every input. No computed mean/source/output estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff ENNReal Topology BigOperators TensorProduct
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
variable {Β : Type*} [Fintype Β]

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

private local instance meanPrimitiveGeometryFirstNormed : NormedAddCommGroup (Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFirstSpace : NormedSpace ℝ (Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryHessianNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryHessianSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryT0Normed : NormedAddCommGroup (Es →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveGeometryT0Space : NormedSpace ℝ (Es →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCjetNormed : NormedAddCommGroup (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCjetSpace : NormedSpace ℝ (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanPrimitiveCANormed : NormedAddCommGroup
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCASpace : NormedSpace ℝ
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
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

theorem round3Parameter_original_canonical_raw_observer
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (rho : ℝ) (hrho : 0 < rho)
    (n q s Rsub Lprimary : ℕ) (horder : s+1 ≤ n)
    (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (z : Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT
      Tinv Forward Meta Rsub Lprimary i)
    (hGR : (univ : Set (P × M)) ⊆ incrementsOriginalParameterRegion Data)
    (input : Bool → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hInput : ∀ a i, ∃ U : Set (Fin (m+1+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a) i) U)
    (hSymm : ∀ a (z : P × M), (input a z.1 z.2).IsSymm)
    (hpos : ∀ a nu z, z ∈ (univ : Set (P × M)) → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      rho/4 < Data.linearArgument nu z.1 z.2 (input a z.1 z.2))
    (hdec : ∀ a z, z ∈ (univ : Set (P × M)) → input a z.1 z.2 =
      incrementsOriginalDecompositionTensor Data z.1 z.2 (input a z.1 z.2))
    (harg : ∀ a nu, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : P × M => Data.linearArgument nu z.1 z.2 (input a z.1 z.2))
      ((univ : Set (P × M)) ∩ Data.primaryDomain nu))
    (R Delta epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) (hDelta : 0 ≤ Delta)
    (hInputFin : ∀ a, paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hInputBound : ∀ a, (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ max 0 R)
    (hDiffFin : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hDiffBound : (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ Delta) :
    let Bnd := parameterRound2_identityRawBnd m d N n (Packet n) c cT
      (1+Forward n) (Meta n) R Tinv
    let Mg := parameterRound2_identityRawMg m d N n (Packet n) c cT (1+Forward n) Tinv
    let Dinput := parameterRound2_identityRawDinput m d n (Packet n) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    ∃ g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (actualOriginalOpenParameterSlice Data i),
    HEq g0 (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)) ∧
    let W := actualOriginalParameterNeighborhood Data i.2 univ
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 univ isOpen_univ
    Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n (q+2) s Rsub Lprimary (rho/4) Bnd Mg Tfixed
      (actualOriginalOpenParameterSlice Data i) (actualOriginalOpenParameterSlice_contMDiff Data hd hs i)
      (parameterRound2_restrictPrimaryFamily (actualOriginalOpenParameterSlice Data i) g0 W hW)
      (actualOriginalParameterTensorSlice Data i (input true)) (actualOriginalParameterTensorSlice Data i (input false))
      W (fun nu => W ∩ (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu)
      (Data.atlas.chart i.1) (actualRawObserverOpen (Data.atlas.chart i.1) W)
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) (epsilon*ell) ell (Dinput*Delta)) := by
  intro Bnd Mg Dinput Tfixed
  have hCore : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) (actualOriginalGivenInputProfile_core_le Data 0 ell)
  let eta := (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta
  let F := actualOriginalOpenParameterSlice Data i
  let hFn := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
  let g0 := actualOriginalPrimaryFamily Data hd hs hn i z.host z.native z.slices z.data eta z.active
  let W := actualOriginalParameterNeighborhood Data i.2 univ
  let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 univ isOpen_univ
  let gN := parameterRound2_restrictPrimaryFamily F g0 W hW
  have ctrl := round3Parameter_refinement_samples_restrict Data i.2 F g0 z.host z.native
    ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) W
    ((Data.parameterChart i.2).open_target.prod isOpen_univ) hW (fun _ hz => hz.1)
    ell Tinv Forward Meta Rsub Lprimary z.refinement
  have hBn : 0 < 1+Forward n := by linarith [hForward n]
  have hprim (a) : ParameterRound2GlobalMeanPrimitives F hFn gN
      (actualOriginalParameterTensorSlice Data i (input a)) W
      (fun nu => W ∩ (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) ⁻¹' Data.primaryDomain nu) :=
    round3Parameter_original_active_mean_primitives Data hd hs hn hp i z.host z.native z.slices z.data
      eta z.active hImm z.native_open ell c cT (1+Forward n) hell hell1 hEll hcT hBn hCore
      z.transverse univ isOpen_univ hGR (input a) (harg a)
      (fun nu w hw hrel => (div_pos hrho (by norm_num : (0:ℝ)<4)).trans (hpos a nu w hw hrel))
      (fun w _ => hSymm a w) (hdec a) ctrl.eta_smooth ctrl.eta_support ctrl.partition
  have raw := round3Parameter_original_active_raw_profiles_from_primitives Data hd hs hn i
    z.host z.native z.slices z.data eta z.active hImm z.native_open univ isOpen_univ hGR
    (fun _ _ => mem_univ _) input hInput
    (fun a p _ x => hSymm a (p,x)) hLinear
    n (q+2) s Rsub Lprimary horder
    ell (epsilon*ell) (Packet n) (max 0 R) Delta (rho/4) c cT
    (1+Forward n) (Forward n) (Meta n) hell hell1 (mul_pos he hell)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le)
    hDelta (div_pos hrho (by norm_num : (0:ℝ)<4)) (hMeta n) (hForward n)
    (hGiven n) (hPacket n) hInputFin hInputBound hDiffFin hDiffBound
    (fun a nu w hw hrel => (hpos a nu w hw hrel).le) hEll hcT hBn (by linarith)
    z.transverse Tinv hTinv i.1 hprim
    (ctrl.sample_inverse i.1)
    (fun nu a k hk _ => ctrl.inverse_jets i.1 nu a k hk)
    (fun nu a k hk hkn => ctrl.forward_jets n i.1 nu a k hk hkn)
    (fun nu a k hkn => ctrl.eta_jets n i.1 nu a k hkn)
    ctrl.eta_count ctrl.primary_count
  let Told := fun k => actualFastChartTransferCost
    (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d n*Packet n) k*Forward n
  have hFixed := actualOriginalPrimaryFamily_raw_profiles_fixed_transition Data hd hs hn i
    z.host z.native z.slices z.data eta z.active univ isOpen_univ i.1 n (q+2) s Rsub Lprimary
    (rho/4) Bnd Mg Told ell (epsilon*ell) (Dinput*Delta) hell
    Packet Forward hForward hGiven hPacket
    (actualOriginalParameterTensorSlice Data i (input true)) (actualOriginalParameterTensorSlice Data i (input false))
    (fun r nu a k hk hkr => ctrl.forward_jets r i.1 nu a k hk hkr) (Classical.choice raw.2.2.2)
  refine ⟨g0,z.same,?_⟩
  have hT : Tfixed = fun k => actualFastChartTransferCost
      (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d k*Packet k) k*Forward k := rfl
  have hPair : (i.1,i.2) = i := rfl
  simpa only [hT,g0,hPair] using hFixed.2

#print axioms round3Parameter_original_canonical_raw_observer
end GlobalEmbedding.Continuation
