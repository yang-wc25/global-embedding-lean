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

theorem round3Parameter_actual_original_mean_raw_reserve_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hAll : Data.parameterSet = univ)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (ML : ℝ) (hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML)
    (q Rsub Lprimary : ℕ)
    (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n)
    (prep : ∀ i, Round3ParameterOriginalNativeMeanPreparation Data hd hs hn g ell cT
      Tinv Forward Meta Rsub Lprimary i) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W0 := incrementsOriginalParameterRegion Data
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W0 hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    0 < radius ∧ ∀ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0,
      H.val = Data.H → Round3ParameterMeanRawReserveSupply (Tr := ℝ) Data.atlas Data.parameterChart
        S W0 p H radius q Rsub Lprimary (rho/4) Bnd Mg Dinput Tfixed
        (fun p x => Data.F (p,x)) hF g Data.primaryDomain ell := by
  intro S W0 p radius Bnd Mg Dinput Tfixed
  have hBase := parameterRound2_original_germ_reserve_ball (J := Bool) Data hd hLinear hDecomp
    rho hReserve hS ell ML hProfile hML
  have hCore : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) (actualOriginalGivenInputProfile_core_le Data 0 ell)
  refine ⟨hBase.1,?_⟩
  intro H hH epsilon he he1 s R K L hK hL
  let n := s+(q+4)
  let elems : Bool → parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 :=
    fun a => if a then K.val else L.val
  let input := fun a : Bool => (elems a).val
  have hclose : ∀ a, p 0 (elems a-H) < radius := by
    intro a
    cases a
    · exact L.property
    · exact K.property
  obtain ⟨G,hG,hKG,hGR,hpos,hdec,harg⟩ := hBase.2 H hH elems hclose
  have hGAll : G = univ := Set.eq_univ_of_forall (fun z => hKG (by
    exact ⟨by rw [hAll]; exact mem_univ _,mem_univ _⟩))
  subst G
  have hInput (a) : ∀ i, ∃ U : Set (Fin (m+1+d) → ℝ), IsOpen U ∧ S i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a) i) U :=
    (elems a).property.1
  have hSymm : ∀ a z, z ∈ (univ : Set (P × M)) → (input a z.1 z.2).IsSymm :=
    fun a z _ => (elems a).property.2 z (hGR (mem_univ _))
  have hInputFin (a) : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ :=
    parameterRound2_tensorGerm_weighted_finite Data.atlas Data.parameterChart S W0
      hS (fun _ _ hz => hz.1) (elems a) 0 n ell
  have hInputBound (a) : (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ max 0 R := by
    cases a
    · exact hL.trans (le_max_right _ _)
    · exact hK.trans (le_max_right _ _)
  have hDiffFin : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ :=
    parameterRound2_tensorGerm_weighted_finite Data.atlas Data.parameterChart S W0
      hS (fun _ _ hz => hz.1) (K.val-L.val) 0 n ell
  refine ⟨univ,isOpen_univ,hGR,(fun _ _ _ => mem_univ _),?_⟩
  apply round3Parameter_original_closed_mean_atlas Data hd hs hAll hF g K.val.val L.val.val
    n q s Rsub Lprimary (rho/4) (Bnd s R) (Mg s) Tfixed (epsilon*ell) ell
      (Dinput s*p n (K.val-L.val))
  intro i
  let z := prep i
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
      (fun nu w hw hrel => (div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)).trans (hpos a nu w hw hrel))
      (hSymm a) (hdec a) ctrl.eta_smooth ctrl.eta_support ctrl.partition
  have raw := round3Parameter_original_active_raw_profiles_from_primitives Data hd hs hn i
    z.host z.native z.slices z.data eta z.active hImm z.native_open univ isOpen_univ hGR
    (fun _ _ => mem_univ _) input hInput
    (fun a p hp x => (elems a).property.2 (p,x) ⟨hp,mem_univ _⟩) hLinear
    n (q+2) s Rsub Lprimary (by dsimp [n]; omega)
    ell (epsilon*ell) (Packet n) (max 0 R) (p n (K.val-L.val)) (rho/4) c cT
    (1+Forward n) (Forward n) (Meta n) hell hell1 (mul_pos he hell)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le)
    (apply_nonneg _ _) (div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)) (hMeta n) (hForward n)
    (hGiven n) (hPacket n) hInputFin hInputBound hDiffFin le_rfl
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
    (rho/4) (Bnd s R) (Mg s) Told ell (epsilon*ell) (Dinput s*p n (K.val-L.val)) hell
    Packet Forward hForward hGiven hPacket
    (actualOriginalParameterTensorSlice Data i (input true)) (actualOriginalParameterTensorSlice Data i (input false))
    (fun r nu a k hk hkr => ctrl.forward_jets r i.1 nu a k hk hkr) (Classical.choice raw.2.2.2)
  refine ⟨g0,z.same,?_⟩
  have hT : Tfixed = fun k => actualFastChartTransferCost
      (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d k*Packet k) k*Forward k := rfl
  have hPair : (i.1,i.2) = i := rfl
  simpa only [input,elems,Bool.false_eq_true,ite_false,ite_true,hT,g0,hPair] using hFixed.2

#print axioms round3Parameter_actual_original_mean_raw_reserve_supply
end GlobalEmbedding.Continuation

