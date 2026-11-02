import Probes.ActualIncrementOriginalPrimitiveBinding
import Probes.ActualIncrementOriginalMeanPrimitives
import Probes.Round3ParameterOriginalFamilyActiveGeometry
import Smoothing.ParameterRound2MeanPrimitives
import Smoothing.ParameterRound2PrimaryRestriction

/-! Qualitative actual mean primitives require NO quantitative native
first-derivative bound: the genuine geometry sample is empty.

The original native positivity/decomposition neighborhood, pulled through
one actual parameter chart, supplies the SAME original mean primitives.
Charts are genuinely restricted to that neighborhood; the previously proved
restriction identities preserve the original actual wave and mean there. -/
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

private theorem actual_original_mean_primitives_from_fields
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
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
    (G : Set (P × M)) (hG : IsOpen G) (hGR : G ⊆ incrementsOriginalParameterRegion Data)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hArgument : ∀ nu, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : P × M => Data.linearArgument nu z.1 z.2 (input z.1 z.2)) (G ∩ Data.primaryDomain nu))
    (hPositive : ∀ nu z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      0 < Data.linearArgument nu z.1 z.2 (input z.1 z.2))
    (hSymm : ∀ z ∈ G, (input z.1 z.2).IsSymm)
    (hDecomp : ∀ z ∈ G, input z.1 z.2 = incrementsOriginalDecompositionTensor Data z.1 z.2 (input z.1 z.2)) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    let g := parameterRound2_restrictPrimaryFamily F g0 W hW
    let primary := fun nu => W ∩
      (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu
    (hEta : ∀ nu beta, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta nu beta) W) →
    (hEtaSupport : ∀ nu beta, incrementsGlobalRelativeSupport W (eta nu beta) ⊆ (g0.chart nu beta).source) →
    (hPartition : ∀ nu z, z ∈ incrementsGlobalRelativeSupport W (g0.cutoff nu) →
      ∀ᶠ w in 𝓝 z, ∑ beta, eta nu beta w = 1) →
    (hGeomG : ∀ nu beta, ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ (g0.inverse nu beta z.1)) z.2)) (g0.chart nu beta).target) →
    (hGeomJ : ∀ nu beta, ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) (g0.inverse nu beta z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g0.inverse nu beta z.1) z.2)) (g0.chart nu beta).target) →
    (hGeomT : ∀ nu beta, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g0.inverse nu beta z.1) z.2) (g0.chart nu beta).target) →
    (hGeomA : ∀ nu beta, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g0.inverse nu beta z.1) z.2) (g0.chart nu beta).target) →
    (hGeomB : ∀ nu beta, ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g0.inverse nu beta z.1) z.2) (g0.chart nu beta).target) →
    (hGeomBR : ∀ nu beta, ContDiffOn ℝ ∞ (fun z : X => fun r : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (g0.inverse nu beta z.1) z.2 0 r : V)) (g0.chart nu beta).target) →
    ParameterRound2GlobalMeanPrimitives F hF g (actualOriginalParameterTensorSlice Data i input) W primary := by
  intro F hF g0 W hW g primary hEta hEtaSupport hPartition hGeomG hGeomJ hGeomT hGeomA hGeomB hGeomBR
  let rho := fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)
  have hWp : ∀ z ∈ W, z.1 ∈ (Data.parameterChart i.2).target := fun _ hz => hz.1.1
  have hWr : MapsTo rho W (incrementsOriginalParameterRegion Data) := fun _ hz => hGR hz.2
  have hRho : ContinuousOn rho W :=
    ((Data.parameterChart i.2).continuousOn_symm.comp continuousOn_fst hWp).prodMk continuousOn_snd
  have hP (nu) : IsOpen (primary nu) := hRho.isOpen_inter_preimage hW (hd.primary_open nu)
  have hsup (nu) := actual_original_parameter_pullback_support Data i.2 W hWp hWr nu
  have hPrimSup (nu) : incrementsGlobalRelativeSupport W (g.cutoff nu) ⊆ primary nu := by
    intro z hz
    exact ⟨by rcases hz with ⟨w,hw,rfl⟩; exact w.property,hd.cutoff_support_local nu (hsup nu z hz)⟩
  have hfield {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (nu) (f : P × M → Y)
      (hf : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Y) ∞ f
        (Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Y) ∞ (f ∘ rho) (W ∩ primary nu) :=
    actual_original_parameter_pullback_smooth Data hd i.2 f _ hf _
      (fun _ hz => hWp _ hz.1) (fun _ hz => ⟨hz.2.2,hWr hz.1⟩)
  refine {
    hW := hW
    hPrimary := hP
    hPrimarySupport := hPrimSup
    hSourceW := ?_
    hChart := ?_
    hChartInv := ?_
    hInverse := ?_
    hCombinedSupport := ?_
    hPhase := fun nu => hfield nu (Data.phase nu) (hs.phase_joint nu)
    hCut := fun nu => hfield nu (Data.cutoff nu) (hs.cutoff_joint nu)
    hNormal := fun nu => hfield nu (Data.freeNormal nu) (hs.normal_joint nu)
    hArgument := ?_
    hEta := hEta
    hPositive := ?_
    hUnit := ?_
    hPartition := hPartition
    hSymm := fun z hz => hSymm (rho z) hz.2
    hDecomp := ?_
    hDouble := ?_
    hInteraction := ?_
    hG := fun nu beta => (hGeomG nu beta).mono (fun _ hz => hz.1)
    hJ := fun nu beta => (hGeomJ nu beta).mono (fun _ hz => hz.1)
    hT0 := fun nu beta => (hGeomT nu beta).mono (fun _ hz => hz.1)
    hA := fun nu beta => (hGeomA nu beta).mono (fun _ hz => hz.1)
    hB := fun nu beta => (hGeomB nu beta).mono (fun _ hz => hz.1)
    hSecond := fun nu beta => (hGeomBR nu beta).mono (fun _ hz => hz.1) }
  · intro nu beta z hz
    exact ⟨hz.2,hz.2,(hactive nu beta z hz.1).1⟩
  · intro nu beta
    exact (hdata nu beta).2.1.mono (fun _ hz => hz.1)
  · intro nu beta
    exact (hdata nu beta).2.2.1.mono (fun _ hz => hz.1)
  · intro nu beta z hz
    exact actualOriginalPrimaryFamily_inverse Data hd hs hn i host b e hdata eta hactive nu beta z hz.1
  · intro nu beta z hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact ⟨hEtaSupport nu beta ⟨w,tsupport_mul_subset_left hw,rfl⟩,w.property⟩
  · intro nu
    exact actual_original_parameter_pullback_smooth Data hd i.2
      (fun z : P × M => Data.linearArgument nu z.1 z.2 (input z.1 z.2)) _
      (hArgument nu) _ (fun _ hz => hWp _ hz.1) (fun _ hz => ⟨hz.1.2,hz.2.2⟩)
  · intro nu z hz
    have hw : z ∈ W := by rcases hz with ⟨w,hw,rfl⟩; exact w.property
    exact hPositive nu (rho z) hw.2 (hsup nu z hz)
  · intro nu z hz hne
    have hsupport : z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu) :=
      ⟨⟨z,hz⟩,subset_tsupport (fun w : W => g.cutoff nu w.val) hne,rfl⟩
    exact hn.unit nu (rho z) ⟨(hPrimSup nu hsupport).2,hWr hz⟩
  · intro z hz v w
    exact actual_original_parameter_decomposition Data i.2 input z (hDecomp (rho z) hz.2) v w
  · intro nu z hz
    have ho := hsup nu z hz
    have ha : rho z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local nu ho,incrementsOriginalRelativeCutoffSupport_subset Data nu ho⟩
    change (tangentSpaceCastModel 𝓘(ℝ,ℝ) _).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => Data.phase nu ((rho z).1,y)+Data.phase nu ((rho z).1,y)) z.2) ≠ 0
    rw [actual_original_phase_sum_covector Data hd hs nu nu (rho z).1 z.2 ha ha,← two_smul ℝ]
    exact (hp.doubled_good nu (rho z) ha).1
  · intro nu mu hne z hnu hmu
    have hn0 := hsup nu z hnu
    have hm0 := hsup mu z hmu
    have han : rho z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local nu hn0,incrementsOriginalRelativeCutoffSupport_subset Data nu hn0⟩
    have ham : rho z ∈ Data.primaryDomain mu ∩ incrementsOriginalParameterRegion Data :=
      ⟨hd.cutoff_support_local mu hm0,incrementsOriginalRelativeCutoffSupport_subset Data mu hm0⟩
    constructor
    · change (tangentSpaceCastModel 𝓘(ℝ,ℝ) _).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => Data.phase nu ((rho z).1,y)+Data.phase mu ((rho z).1,y)) z.2) ≠ 0
      rw [actual_original_phase_sum_covector Data hd hs nu mu (rho z).1 z.2 han ham]
      simpa only [ite_true,one_smul] using (hp.interaction_good nu mu hne true (rho z) ⟨hn0,hm0⟩).1
    · change (tangentSpaceCastModel 𝓘(ℝ,ℝ) _).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun y => Data.phase nu ((rho z).1,y)-Data.phase mu ((rho z).1,y)) z.2) ≠ 0
      rw [actual_original_phase_sub_covector Data hd hs nu mu (rho z).1 z.2 han ham]
      have hneg : (-1:ℝ) • incrementsOriginalPhaseCovector Data mu (rho z).1 z.2 =
          -incrementsOriginalPhaseCovector Data mu (rho z).1 z.2 := by
        ext v
        simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,smul_eq_mul,neg_one_mul]
      have hnonzero := (hp.interaction_good nu mu hne false (rho z) ⟨hn0,hm0⟩).1
      change incrementsOriginalPhaseCovector Data nu (rho z).1 z.2 +
        (-1:ℝ) • incrementsOriginalPhaseCovector Data mu (rho z).1 z.2 ≠ 0 at hnonzero
      rw [hneg,← sub_eq_add_neg] at hnonzero
      exact hnonzero


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


theorem round3Parameter_original_active_mean_primitives
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
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
    (hTreserve : ∀ nu beta z, z ∈ (b nu beta).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e nu beta z.1).symm z.2 v‖^2)
    (G : Set (P × M)) (hG : IsOpen G) (hGR : G ⊆ incrementsOriginalParameterRegion Data)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hArgument : ∀ nu, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : P × M => Data.linearArgument nu z.1 z.2 (input z.1 z.2)) (G ∩ Data.primaryDomain nu))
    (hPositive : ∀ nu z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      0 < Data.linearArgument nu z.1 z.2 (input z.1 z.2))
    (hSymm : ∀ z ∈ G, (input z.1 z.2).IsSymm)
    (hDecomp : ∀ z ∈ G, input z.1 z.2 = incrementsOriginalDecompositionTensor Data z.1 z.2 (input z.1 z.2)) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    let g := parameterRound2_restrictPrimaryFamily F g0 W hW
    let primary := fun nu => W ∩
      (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu
    (hEta : ∀ nu beta, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta nu beta) W) →
    (hEtaSupport : ∀ nu beta, incrementsGlobalRelativeSupport W (eta nu beta) ⊆ (g0.chart nu beta).source) →
    (hPartition : ∀ nu z, z ∈ incrementsGlobalRelativeSupport W (g0.cutoff nu) →
      ∀ᶠ w in 𝓝 z, ∑ beta, eta nu beta w = 1) →
    ParameterRound2GlobalMeanPrimitives F hF g (actualOriginalParameterTensorSlice Data i input) W primary := by
  intro F hF g0 W hW g primary hEta hEtaSupport hPartition
  have hgeom (nu : Fin Data.primaryCount) (beta : Β) :=
    round3Parameter_original_family_active_geometry_profiles (fun _ => 0) (fun _ => le_refl 0) 0
      Data hd hs hn i host b e hdata eta hactive hImm nu beta ∅ (empty_subset _)
      (hsource nu beta) (fun z hz => False.elim hz)
      ell (incrementsOriginalCoreInputProfile Data 0 ell).toReal c cT Bnative
      hell hell1 hEll hcT hBnative hfinite le_rfl (fun z hz => False.elim hz)
      (hTreserve nu beta) (fun k hk hkj z hz => False.elim hz)
  exact actual_original_mean_primitives_from_fields Data hd hs hn hp i host b e hdata eta hactive
    G hG hGR input hArgument hPositive hSymm hDecomp hEta hEtaSupport hPartition
    (fun nu beta => (hgeom nu beta).2.2.1.1)
    (fun nu beta => (hgeom nu beta).2.2.2.1.1)
    (fun nu beta => (hgeom nu beta).2.2.2.2.1.1)
    (fun nu beta => (hgeom nu beta).2.2.2.2.2.2.1.1)
    (fun nu beta => (hgeom nu beta).2.2.2.2.2.2.2.1)
    (fun nu beta => (hgeom nu beta).2.2.2.2.2.1.1)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_active_mean_primitives
