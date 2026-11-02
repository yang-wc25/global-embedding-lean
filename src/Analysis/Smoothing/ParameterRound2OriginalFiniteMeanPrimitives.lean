import Probes.ActualIncrementOriginalMeanPrimitives
import Smoothing.ParameterRound2OriginalFiniteReserveGermSmooth

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

variable [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]

private local instance meanPrimitiveTangentNormed (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance meanPrimitiveTangentSpace (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance
private local instance meanPrimitiveTangentInner (x : M) : InnerProductSpace ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x) := inferInstance

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

variable {J : Type*} [Fintype J]

theorem parameterRound2_original_finite_mean_primitives
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
    (ell c margin Bhost Bnative : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hmarginPos : 0 < margin) (hBhost : 0 < Bhost) (hBnative : 0 < Bnative)
    (hfinite : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤)
    (hhost : ∀ nu beta w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ‖(tangentSpaceCastModel 𝓙 (Data.atlas.chart (host nu beta) w.2)).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓙 (Data.atlas.chart (host nu beta)) w.2)‖ ≤ Bhost)
    (hnative : ∀ nu beta z, z ∈ (b nu beta).source → ‖fderiv ℝ (b nu beta) z‖ ≤ Bnative)
    (hmargin : ∀ nu beta w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ∀ (hp : (Data.parameterChart i.2).symm w.1 ∈ Data.parameterOpen),
      let p := (Data.parameterChart i.2).symm w.1
      let xi := incrementsOriginalPhaseCovector Data nu p w.2
      ∀ v : SymmetricSquare xi.ker, margin*‖v‖ ≤
        ‖covectorRestriction (trueSecondFormL (fun y => Data.F (p,y))
          (incrementsOriginal_slice_contMDiff Data hd hs p hp) w.2) xi v‖)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecompOriginal : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (input : J → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hSymm : ∀ a, ∀ p ∈ Data.parameterOpen, ∀ x, (input a p x).IsSymm)
    (hInput : ∀ a v, ∃ U : Set (Fin (m+1+d) → ℝ), IsOpen U ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet v ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a) v) U)
    (ML R : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML)
    (hDiffFinite : ∀ a, paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input a p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hR : ∀ a, (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input a p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ R)
    (hSmall : ‖actualOriginalCoefficientFunctional (m+1)‖*ML*R ≤ rho/2) :
    ∃ (G : Set (P × M)) (hG : IsOpen G),
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
      G ⊆ incrementsOriginalParameterRegion Data ∧
      (∀ a nu z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
        rho/4 < Data.linearArgument nu z.1 z.2 (input a z.1 z.2)) ∧
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
    ∀ a, ParameterRound2GlobalMeanPrimitives F hF g
      (actualOriginalParameterTensorSlice Data i (input a)) W primary := by
  obtain ⟨G,hG,hKG,hGR,hpos,hdec,harg⟩ :=
    parameterRound2_original_finite_joint_smooth_reserve_from_germ_inputs Data hd hLinear
      hDecompOriginal rho hReserve input hSymm hInput ell ML R hProfile hML hDiffFinite hR hSmall
  refine ⟨G,hG,hKG,hGR,hpos,?_⟩
  intro F hF g0 W hW g primary hEta hEtaSupport hPartition a
  exact actualOriginalPrimaryFamily_mean_primitives Data hd hs hn hp i host b e hdata eta hactive
    hImm hsource ell c margin Bhost Bnative hell hell1 hEll hmarginPos hBhost hBnative hfinite
    hhost hnative hmargin G hG hGR (input a) (harg a)
    (fun nu z hz hrel => (div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)).trans
      (hpos a nu z hz hrel))
    (fun z hz => hSymm a z.1 (hGR hz).1 z.2) (hdec a) hEta hEtaSupport hPartition

#print axioms parameterRound2_original_finite_mean_primitives
end GlobalEmbedding.Continuation
