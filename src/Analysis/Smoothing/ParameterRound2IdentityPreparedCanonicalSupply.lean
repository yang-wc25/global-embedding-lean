import Smoothing.ParameterRound2IdentityNativeReservePrimitives
import Smoothing.ParameterRound2MeanRawPreparedCanonicalSupply
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

variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
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

theorem parameterRound2_identity_original_prepared_canonical_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart i.2 = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hsource : ∀ nu beta, (b nu beta).source ⊆ actualOriginalNativeOpen Data (host nu beta,i.2))
    (ell c cT Bnative : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hcT : 0 < cT) (hBnative : 0 < Bnative)
    (hfinite : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤)
    (hnative : ∀ nu beta z, z ∈ (b nu beta).source → ‖fderiv ℝ (b nu beta) z‖ ≤ Bnative)
    (hTreserve : ∀ nu beta z, z ∈ (b nu beta).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e nu beta z.1).symm z.2 v‖^2)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecompOriginal : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (Vprep : Set (Ep × M)) (hVprep : IsOpen Vprep)
    (hKVprep : Data.parameterSet ×ˢ (univ : Set M) ⊆ Vprep)
    (hS : ∀ v, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet v))
    (ML : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML)
    (q Rsub Lprimary : ℕ)
    (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    ParameterRound2IdentityRefinementSamples Data i.2 F g0 host b Vprep ell Tinv Forward Meta Rsub Lprimary →
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W0 := incrementsOriginalParameterRegion Data
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W0 hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT Bnative (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4))) c cT Bnative Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    0 < radius ∧ ∀ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0,
    H.val = Data.H →
    ParameterRound2MeanRawPreparedCanonicalSupply (Tr := ℝ) Data.atlas Data.parameterChart S W0 Vprep p H radius
      q Rsub Lprimary (rho/4) Bnd Mg Dinput Tfixed F hF g0 Data.primaryDomain ell := by
  classical
  intro F hF g0 hRef S W0 p radius Bnd Mg Dinput Tfixed
  letI : Subsingleton (Fin Data.parameterCount) := by rw [hOne]; infer_instance
  have hBase := parameterRound2_identity_native_reserve_primitives Data hd hs hn hp i hId
    host b e hdata eta hactive hImm hsource ell c cT Bnative hell hell1 hEll hcT hBnative hfinite
    hnative hTreserve hLinear hDecompOriginal rho hReserve Vprep hVprep hKVprep hS ML hProfile hML
  refine ⟨hBase.1,?_⟩
  intro H hH K L
  let input := fun a : Bool => if a then K.val.val else L.val.val
  let elems : Bool → parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 :=
    fun a => if a then K.val else L.val
  have hinput (a) : (elems a).val = input a := by cases a <;> rfl
  obtain ⟨G,hG,hKG,hGR,hGP,hSG,hpos,hprim⟩ := hBase.2 H hH K L
  have ctrl := parameterRound2_identity_refinement_samples_restrict Data i.2 F g0 host b
    Vprep G hVprep hG hGP ell Tinv Forward Meta Rsub Lprimary hRef
  let g := parameterRound2_restrictPrimaryFamily F g0 G hG
  have prim (a) : ParameterRound2GlobalMeanPrimitives F hF g (input a) G Data.primaryDomain :=
    hprim ctrl.eta_smooth ctrl.eta_support ctrl.partition a
  have primInter (a) := parameterRound2_mean_primitives_inter_primary F hF g (input a) G Data.primaryDomain (prim a)
  have hW : actualOriginalParameterNeighborhood Data i.2 G = G :=
    parameterRound2_identity_parameter_neighborhood Data i.2 hId G
  have heq : (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) = id := by
    funext z
    simp only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq]
  let Obs := fun v : Fin Data.atlas.count × Fin Data.parameterCount => actualRawObserverOpen (Data.atlas.chart v.1) G
  have hObs : ∀ v, Obs v ⊆ (Data.parameterChart v.2).source ×ˢ (Data.atlas.chart v.1).target := by
    intro v z hz
    have hip : v.2 = i.2 := Subsingleton.elim _ _
    refine ⟨?_,hz.1.2⟩
    rw [hip,hId]
    exact mem_univ _
  refine ⟨G,hG,hGR,hGP,hSG,hObs,?_⟩
  intro epsilon he he1 s R hK hL
  let n := s+(q+4)
  have hInputs : ∀ a v, ∃ U : Set (Fin (m+1+d) → ℝ), IsOpen U ∧ S v ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a) v) U := by
    intro a v
    simpa only [hinput] using (elems a).property.1 v
  have hSymms : ∀ a p, p ∈ Data.parameterOpen → ∀ x, (input a p x).IsSymm := by
    intro a p hp x
    simpa only [hinput] using (elems a).property.2 (p,x) ⟨hp,mem_univ _⟩
  have hInputFin (a) : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ := by
    simpa only [hinput] using parameterRound2_tensorGerm_weighted_finite Data.atlas Data.parameterChart S W0
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
  refine ⟨?_⟩
  rintro ⟨observer,ip⟩
  have hip : ip = i.2 := Subsingleton.elim _ _
  subst ip
  have hraw := actualOriginalPrimaryFamily_native_raw_profiles_from_primitives Data hd hs hn i host b e hdata
    eta hactive hImm hsource G hG hGR hKG input hInputs hSymms hLinear n (q+2) s Rsub Lprimary (by dsimp [n]; omega)
    ell (epsilon*ell) (Packet n) (max 0 R) (p n (K.val-L.val)) (rho/4) c cT Bnative (Forward n) (Meta n)
    hell hell1 (mul_pos he hell) (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le)
    (apply_nonneg _ _) (div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)) (hMeta n) (hForward n)
    (hGiven n) (hPacket n) hInputFin hInputBound hDiffFin le_rfl
    (fun a nu z hz hrel => (hpos a nu z hz hrel).le) hEll hcT hBnative hnative hTreserve
    Tinv hTinv observer
  have hprim' : ∀ a, ParameterRound2GlobalMeanPrimitives F hF
      (parameterRound2_restrictPrimaryFamily F g0 (actualOriginalParameterNeighborhood Data i.2 G)
        (actualOriginalParameterNeighborhood_isOpen Data i.2 G hG))
      (actualOriginalParameterTensorSlice Data i (input a))
      (actualOriginalParameterNeighborhood Data i.2 G)
      (fun nu => actualOriginalParameterNeighborhood Data i.2 G ∩
        (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu) := by
    intro a
    simpa only [hW,parameterRound2_identity_parameter_tensor_slice Data i hId,heq,preimage_id] using primInter a
  have hraw' := hraw hprim'
  simp only [hW] at hraw'
  have hrawFull := hraw'
    (ctrl.sample_inverse observer)
    (fun nu beta k hk hkn => ctrl.inverse_jets observer nu beta k hk)
    (fun nu beta k hk hkn => ctrl.forward_jets n observer nu beta k hk hkn)
    (fun nu beta k hkn => ctrl.eta_jets n observer nu beta k hkn)
    ctrl.eta_count ctrl.primary_count
  let raw := Classical.choice hrawFull.2.2.2
  let Told := fun k => actualFastChartTransferCost
    (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d n*Packet n) k*Forward n
  have hfixed := actualOriginalPrimaryFamily_raw_profiles_fixed_transition Data hd hs hn i host b e hdata eta hactive
    G hG observer n (q+2) s Rsub Lprimary (rho/4) (Bnd s R) (Mg s) Told ell (epsilon*ell)
    (Dinput s*p n (K.val-L.val)) hell Packet Forward hForward hGiven hPacket
    (actualOriginalParameterTensorSlice Data i (input true)) (actualOriginalParameterTensorSlice Data i (input false))
  simp only [hW] at hfixed
  have hfixedFull := hfixed (fun r nu beta k hk hkr => ctrl.forward_jets r observer nu beta k hk hkr) raw
  let fixed := Classical.choice hfixedFull.2
  have fixedSpec := fixed
  simp only [parameterRound2_identity_parameter_tensor_slice Data i hId,heq,preimage_id] at fixedSpec
  have fixed' := parameterRound2_raw_profiles_fixed_primary n (q+2) s Rsub Lprimary
    (rho/4) (Bnd s R) (Mg s) Tfixed F hF g (input true) (input false) G Data.primaryDomain
    hd.primary_open (Data.atlas.chart observer) (Obs (observer,i.2))
    ((parameterTensorModelEquiv (m+1) d) ⁻¹' S (observer,i.2)) (epsilon*ell) ell
    (Dinput s*p n (K.val-L.val)) fixedSpec
  simpa only [parameterRound2_identity_parameter_sample_image _ hId,n,input,g,Bool.false_eq_true,ite_false,ite_true] using fixed'

#print axioms parameterRound2_identity_original_prepared_canonical_supply
end GlobalEmbedding.Continuation
