import Probes.ActualIncrementOriginalNativeRawProfiles
import Smoothing.ParameterRound2OriginalFiniteMeanPrimitives
import Probes.ActualIncrementOriginalFamilyFields
import Probes.ActualIncrementRawObserverDomains
import Probes.ActualOriginalObserverAdaptedJets
import Probes.ActualOriginalObserverPhaseJets
import Smoothing.ParameterRound2OriginalHostArgument
import Smoothing.ParameterRound2OriginalHostArgumentDifference
import Smoothing.ParameterRound2OriginalObserverArgument
import Smoothing.ParameterRound2OriginalObserverArgumentDifference
import Smoothing.ParameterRound2ScalarRawInput

/-! The SAME actual original family is consumed by the original raw mean
profile. Every geometry, cutoff, normal and linear-argument jet is produced
from the genuine original norms. The only chart/cutoff quantitative inputs
are the actual produced refinement fields; actual sample maps stay explicit.
The given-data profile is displayed separately from the unchanged Core. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle Filter
open scoped ContDiff Topology BigOperators TensorProduct ENNReal Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance marginSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance marginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

variable {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance adaptedGeometryFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance adaptedGeometryT0Normed : NormedAddCommGroup (D →L[ℝ] Tdata) := inferInstance
private local instance adaptedGeometryT0Space : NormedSpace ℝ (D →L[ℝ] Tdata) := inferInstance
private local instance marginCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance marginCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance marginCjetNormed : NormedAddCommGroup (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCjetSpace : NormedSpace ℝ (D →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCANormed : NormedAddCommGroup
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCASpace : NormedSpace ℝ
    ((D →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance marginCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance marginCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace

private local instance rawCoeffInnerNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffInnerSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance rawCoeffOuterNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance rawCoeffOuterSpace : NormedSpace ℝ
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {Β : Type*} [Fintype Β]


private theorem original_weighted_zero_le {ι : Type*} [Fintype ι] {a q : ℕ}
    (base j : ℕ) (ell : ℝ) (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ)) :
    paperAtlasWeighted base 0 ell f O S ≤ paperAtlasWeighted base j ell f O S := by
  simpa only [paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,pow_zero,one_mul,zero_add]
    using parameterPaperAtlasCj_base_le_weighted base j ell f O S

private theorem original_core_zero_le
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (j : ℕ) (ell : ℝ) :
    incrementsOriginalCoreInputProfile Data 0 ell ≤ incrementsOriginalCoreInputProfile Data j ell := by
  unfold incrementsOriginalCoreInputProfile
  exact max_le_max (original_weighted_zero_le _ _ _ _ _ _)
    (max_le_max (original_weighted_zero_le _ _ _ _ _ _)
      (iSup_mono (fun _ => max_le_max (original_weighted_zero_le _ _ _ _ _ _)
        (max_le_max (original_weighted_zero_le _ _ _ _ _ _) (original_weighted_zero_le _ _ _ _ _ _)))))

private theorem original_linear_zero_le
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (j : ℕ) (ell : ℝ) :
    incrementsOriginalInputProfileWithLinear Data 0 ell ≤ incrementsOriginalInputProfileWithLinear Data j ell := by
  unfold incrementsOriginalInputProfileWithLinear
  exact max_le_max (original_core_zero_le Data j ell)
    (iSup_mono (fun _ => original_weighted_zero_le _ _ _ _ _ _))

/-! Original C0 reserve and genuine native inputs produce the common positive
neighborhood and every raw profile field for the same actual primary family. -/

theorem actualOriginalPrimaryFamily_native_raw_profiles_from_original_inputs
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M D)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hsource : ∀ nu beta, (b nu beta).source ⊆ actualOriginalNativeOpen Data (host nu beta,i.2))
    (input : Bool → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hInput : ∀ q a, ∃ UI : Set (Fin (m+1+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input q) a) UI)
    (hSymm : ∀ q p, p ∈ Data.parameterOpen → ∀ x, (input q p x).IsSymm)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecompOriginal : IncrementsOriginalQualitativeDecompositionInputs Data)
    (n length j Rsub Lprimary : ℕ) (horder : j+1 ≤ n)
    (ell tau packet Minput Delta rho c cT Bnative Bforward Meta : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hDelta : 0 ≤ Delta) (hMeta : 0 ≤ Meta) (hBforward : 0 ≤ Bforward)
    (hGiven : actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : (actualOriginalGivenInputProfile Data n ell).toReal ≤ packet)
    (hInputFinite : ∀ q, paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input q))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hMinput : ∀ q, (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input q))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ Minput)
    (hDiffFinite : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hDinput : (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ Delta)
    (hOriginalReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hcT : 0 < cT) (hBnative : 0 < Bnative)
    (hnative : ∀ nu beta z, z ∈ (b nu beta).source → ‖fderiv ℝ (b nu beta) z‖ ≤ Bnative)
    (hTreserve : ∀ nu beta z, z ∈ (b nu beta).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e nu beta z.1).symm z.2 v‖^2)
    (Rinput : ℝ)
    (hC0Finite : ∀ q, paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input q p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤)
    (hC0 : ∀ q, (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input q p x-Data.H p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)).toReal ≤ Rinput)
    (hSmall : ‖actualOriginalCoefficientFunctional (m+1)‖*packet*Rinput ≤ rho/2)
    (Tinv : ℕ → ℝ) (hTinv : ∀ k, 0 ≤ Tinv k) (observer : Fin Data.atlas.count) :
    ∃ (G : Set (P × M)) (hG : IsOpen G),
    Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧ G ⊆ incrementsOriginalParameterRegion Data ∧
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    let W := actualOriginalParameterNeighborhood Data i.2 G
    let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
    let g := parameterRound2_restrictPrimaryFamily F g0 W hW
    let Ainput := fun q => actualOriginalParameterTensorSlice Data i (input q)
    let primary := fun nu => W ∩
      (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) ⁻¹' Data.primaryDomain nu
    let obs := Data.atlas.chart observer
    let oi := (observer,i.2)
    let a := parameterTensorModelEquiv (m+1) d
    let kappa := fun z : X => (z.1,obs.symm z.2)
    let O := actualRawObserverOpen obs W
    let S := a ⁻¹' incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet oi
    let Omega := fun nu => O ∩ kappa ⁻¹' primary nu
    let U := fun nu beta => O ∩ kappa ⁻¹' (g.chart nu beta).source
    let R := fun nu => S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W (g.cutoff nu)
    let Rloc := fun nu beta => R nu ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta nu beta z*g.cutoff nu z)
    let Sloc := fun nu beta => (g.chart nu beta ∘ kappa) '' Rloc nu beta
    (hEta : ∀ nu beta, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (eta nu beta) W) →
    (hEtaSupport : ∀ nu beta, incrementsGlobalRelativeSupport W (eta nu beta) ⊆ (g0.chart nu beta).source) →
    (hPartition : ∀ nu z, z ∈ incrementsGlobalRelativeSupport W (g0.cutoff nu) →
      ∀ᶠ w in 𝓝 z, ∑ beta, eta nu beta w = 1) →
    (hsample : ∀ nu beta, MapsTo (b nu beta).symm (Sloc nu beta) (a ⁻¹'
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet (host nu beta,i.2))) →
    (hinvjet : ∀ nu beta k, 1 ≤ k → k ≤ n+2 → ∀ z ∈ Sloc nu beta,
      ell^(k-1)*‖iteratedFDeriv ℝ k (b nu beta).symm z‖ ≤ Tinv k) →
    (hForward : ∀ nu beta k, 1 ≤ k → k ≤ n+1 → ∀ z ∈ Rloc nu beta,
      ell^(k-1)*‖iteratedFDeriv ℝ k (b nu beta) (actualOriginalObserverHostTransition Data oi (host nu beta) z)‖ ≤ Bforward) →
    (hEtaProduced : ∀ nu beta k, k ≤ n → ∀ z ∈ Sloc nu beta,
      ell^k*‖iteratedFDeriv ℝ k (eta nu beta ∘ (g0.chart nu beta).symm) z‖ ≤ Meta) →
    (hEtaCount : ∀ nu w, w ∈ W → (Finset.univ.filter
      (fun beta => w ∈ incrementsGlobalRelativeSupport W (eta nu beta))).card ≤ Rsub) →
    (hPrimaryCount : ∀ w ∈ W, (Finset.univ.filter
      (fun nu => w ∈ incrementsGlobalRelativeSupport W (g0.cutoff nu))).card ≤ Lprimary) →
    let Cmap := actualOriginalMapJetCost (m+1) d N n*packet
    let Mg := actualAdaptedUniformGeometryCost m N n Tinv c cT Bnative Cmap Cmap
    let Clocal := actualFastChartTransferPrefix (fun k => ‖a.toContinuousLinearMap‖*Tinv k) n *
      coordinateDimensionFactor (m+1+d) n
    let Cobs := actualFastChartTransferPrefix (fun _ => ‖a.toContinuousLinearMap‖) n *
      coordinateDimensionFactor (m+1+d) n
    let Dlocal := 2^n*‖actualOriginalCoefficientFunctional (m+1)‖*Clocal^2*packet
    let Dobs := 2^n*‖actualOriginalCoefficientFunctional (m+1)‖*Cobs^2*packet
    let Dinput := Dlocal+Dobs
    let CutLocal := actualFastChartTransferPrefix Tinv n*(actualOriginalCutoffJetCost (m+1) d n*packet)
    let NormalLocal := actualFastChartTransferPrefix Tinv n*(actualOriginalNormalJetCost (m+1) d N n*packet)
    let CutObs := actualOriginalCutoffJetCost (m+1) d n*packet
    let NormalObs := actualOriginalNormalJetCost (m+1) d N n*packet
    let GradObs := actualOriginalTotalPhaseJetCost (m+1) d n*packet
    let Bnd := 1+|Mg|+|CutLocal|+|NormalLocal|+|CutObs|+|NormalObs|+|Meta|+|GradObs|+Dinput*Minput
    let Tobs := fun k => actualFastChartTransferCost
      (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d n*packet) k*Bforward
    0 ≤ Bnd ∧ 0 ≤ Mg ∧ 0 ≤ Dinput ∧
      Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := ℝ) n length j Rsub Lprimary
        (rho/4) Bnd Mg Tobs F hF g (Ainput true) (Ainput false) W primary obs O S tau ell (Dinput*Delta)) := by
  have hCoreLe := (original_core_zero_le Data n ell).trans (actualOriginalGivenInputProfile_core_le Data n ell)
  have hCore0 : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤ := ne_top_of_le_ne_top hGiven hCoreLe
  have hLinearLe := (original_linear_zero_le Data n ell).trans (actualOriginalGivenInputProfile_linear_le Data n ell)
  have hLinear0 : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤ := ne_top_of_le_ne_top hGiven hLinearLe
  have hLinearBound : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ packet :=
    (ENNReal.toReal_mono hGiven hLinearLe).trans hPacket
  obtain ⟨G,hG,hKG,hGR,hpos,hdec,harg⟩ :=
    parameterRound2_original_finite_joint_smooth_reserve_from_germ_inputs Data hd hLinear
      hDecompOriginal rho hOriginalReserve input hSymm hInput ell packet Rinput
      hLinear0 hLinearBound hC0Finite hC0 hSmall
  refine ⟨G,hG,hKG,hGR,?_⟩
  intro F hF g0 W hW g Ainput primary obs oi a kappa O S Omega U R Rloc Sloc
    hEta hEtaSupport hPartition hsample hinvjet hForward hEtaProduced hEtaCount hPrimaryCount
  have hprim (q : Bool) : ParameterRound2GlobalMeanPrimitives F hF g (Ainput q) W primary :=
    actualOriginalPrimaryFamily_native_mean_primitives Data hd hs hn hp i host b e hdata eta hactive
      hImm hsource ell c cT Bnative hell hell1 hEll hcT hBnative hCore0 hnative hTreserve
      G hG hGR (input q) (harg q)
      (fun nu z hz hrel => (div_pos hOriginalReserve.reserve_pos (by norm_num : (0:ℝ)<4)).trans
        (hpos q nu z hz hrel))
      (fun z hz => hSymm q z.1 (hGR hz).1 z.2) (hdec q) hEta hEtaSupport hPartition
  exact actualOriginalPrimaryFamily_native_raw_profiles_from_primitives Data hd hs hn i host b e hdata
    eta hactive hImm hsource G hG hGR hKG input hInput hSymm hLinear n length j Rsub Lprimary horder
    ell tau packet Minput Delta (rho/4) c cT Bnative Bforward Meta hell hell1 htau htaul hDelta
    (div_pos hOriginalReserve.reserve_pos (by norm_num : (0:ℝ)<4)) hMeta hBforward
    hGiven hPacket hInputFinite hMinput hDiffFinite hDinput
    (fun q nu z hz hsupp => (hpos q nu z hz hsupp).le) hEll hcT hBnative
    hnative hTreserve Tinv hTinv observer
    hprim hsample hinvjet hForward hEtaProduced hEtaCount hPrimaryCount

#print axioms actualOriginalPrimaryFamily_native_raw_profiles_from_original_inputs
end GlobalEmbedding.Continuation
