import Probes.ActualIncrementOriginalNativeMeanPrimitives
import Smoothing.ParameterRound2IdentityParameter
import Smoothing.ParameterRound2PrimaryDomainNormalization

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

theorem parameterRound2_identity_native_reserve_primitives
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart i.2 = OpenPartialHomeomorph.refl Ep)
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
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W0 := incrementsOriginalParameterRegion Data
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W0 hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    0 < radius ∧ ∀ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0,
    H.val = Data.H →
    ∀ K L : {A : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 // p 0 (A-H) < radius},
    let input := fun q : Bool => if q then K.val.val else L.val.val
    ∃ (G : Set (Ep × M)) (hG : IsOpen G),
    Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧ G ⊆ W0 ∧ G ⊆ Vprep ∧
    (∀ v, MapsTo (incrementsOriginalJointPoint Data.atlas Data.parameterChart v) (S v) G) ∧
    (∀ a nu z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      rho/4 < Data.linearArgument nu z.1 z.2 (input a z.1 z.2)) ∧
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let g := parameterRound2_restrictPrimaryFamily F g0 G hG
    (hEta : ∀ nu beta, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta nu beta) G) →
    (hEtaSupport : ∀ nu beta, incrementsGlobalRelativeSupport G (eta nu beta) ⊆ (g0.chart nu beta).source) →
    (hPartition : ∀ nu z, z ∈ incrementsGlobalRelativeSupport G (g0.cutoff nu) →
      ∀ᶠ w in 𝓝 z, ∑ beta, eta nu beta w = 1) →
    ∀ a, ParameterRound2GlobalMeanPrimitives F hF g (input a) G Data.primaryDomain := by
  intro S W0 p radius
  have hr := parameterRound2_original_germ_reserve_ball (J := Bool) Data hd hLinear hDecompOriginal
    rho hReserve hS ell ML hProfile hML
  refine ⟨hr.1,?_⟩
  intro H hH K L input
  let inputs : Bool → parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 :=
    fun a => if a then K.val else L.val
  have hclose : ∀ a, p 0 (inputs a-H) < radius := by
    intro a
    cases a
    · exact L.property
    · exact K.property
  obtain ⟨G0,hG0,hKG0,hGR0,hpos0,hdec0,harg0⟩ := hr.2 H hH inputs hclose
  let G := G0 ∩ Vprep
  have hG : IsOpen G := hG0.inter hVprep
  have hKG : Data.parameterSet ×ˢ (univ : Set M) ⊆ G := fun z hz => ⟨hKG0 hz,hKVprep hz⟩
  have hGR : G ⊆ incrementsOriginalParameterRegion Data := fun z hz => hGR0 hz.1
  have hpos : ∀ a nu z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      rho/4 < Data.linearArgument nu z.1 z.2 ((inputs a).val z.1 z.2) :=
    fun a nu z hz hrel => hpos0 a nu z hz.1 hrel
  have hdec : ∀ a z, z ∈ G → (inputs a).val z.1 z.2 =
      incrementsOriginalDecompositionTensor Data z.1 z.2 ((inputs a).val z.1 z.2) :=
    fun a z hz => hdec0 a z hz.1
  have harg : ∀ a nu, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : Ep × M => Data.linearArgument nu z.1 z.2 ((inputs a).val z.1 z.2))
      (G ∩ Data.primaryDomain nu) :=
    fun a nu => (harg0 a nu).mono (fun z hz => ⟨hz.1.1,hz.2⟩)
  have hinput (a) : (inputs a).val = input a := by cases a <;> rfl
  have hsample : ∀ v, MapsTo (incrementsOriginalJointPoint Data.atlas Data.parameterChart v) (S v) G := by
    intro v z hz
    exact hKG ⟨hz.2.2.2,mem_univ _⟩
  refine ⟨G,hG,hKG,hGR,inter_subset_right,hsample,?_,?_⟩
  · intro a nu z hz hrel
    simpa only [hinput] using hpos a nu z hz hrel
  · intro F hF g0 g hEta hEtaSupport hPartition a
    have hW : actualOriginalParameterNeighborhood Data i.2 G = G :=
      parameterRound2_identity_parameter_neighborhood Data i.2 hId G
    have hEta' : ∀ nu beta, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta nu beta)
        (actualOriginalParameterNeighborhood Data i.2 G) := by simpa only [hW] using hEta
    have hEtaSupport' : ∀ nu beta, incrementsGlobalRelativeSupport
        (actualOriginalParameterNeighborhood Data i.2 G) (eta nu beta) ⊆ (g0.chart nu beta).source := by
      simpa only [hW] using hEtaSupport
    have hPartition' : ∀ nu z, z ∈ incrementsGlobalRelativeSupport
        (actualOriginalParameterNeighborhood Data i.2 G) (g0.cutoff nu) →
        ∀ᶠ w in 𝓝 z, ∑ beta, eta nu beta w = 1 := by simpa only [hW] using hPartition
    have hh := actualOriginalPrimaryFamily_native_mean_primitives Data hd hs hn hp i host b e hdata eta hactive
      hImm hsource ell c cT Bnative hell hell1 hEll hcT hBnative hfinite
      hnative hTreserve G hG hGR (inputs a).val (harg a)
      (fun nu z hz hrel => (div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)).trans
        (hpos a nu z hz hrel))
      (fun z hz => (inputs a).property.2 z (hGR hz)) (hdec a) hEta' hEtaSupport' hPartition'
    have heq : (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) = id := by
      funext z
      simp only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq]
    simp only [hW,parameterRound2_identity_parameter_tensor_slice Data i hId,heq,preimage_id,hinput] at hh
    exact parameterRound2_mean_primitives_fixed_primary F hF g (input a) G Data.primaryDomain hd.primary_open hh

#print axioms parameterRound2_identity_native_reserve_primitives
end GlobalEmbedding.Continuation
