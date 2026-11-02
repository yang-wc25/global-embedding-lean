import Probes.ActualIncrementOriginalNativeMeanPrimitives
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

private theorem original_native_differentiation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X)
    (hp : z.1 ∈ (Data.parameterChart i.2).target) (hx : z.2 ∈ (Data.atlas.chart i.1).target) :
    parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i := by
  have hprod : (incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z),
      incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)) = z :=
    (parameterTensorModelEquiv (m+1) d).symm_apply_apply z
  have hp' := congrArg Prod.fst hprod
  have hx' := congrArg Prod.snd hprod
  dsimp only at hp' hx'
  exact ⟨hx'.symm ▸ hx,hp'.symm ▸ hp⟩

/-- Original input norms and the actual produced refinement fill the literal
RawProfiles. The qualitative primitive records are supplied by
`actualOriginalPrimaryFamily_mean_primitives`, not arbitrary output bounds.
The statement uses the same native P inputs before their fixed chart slices. -/
theorem actualOriginalPrimaryFamily_native_raw_profiles_from_primitives
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
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
    (G : Set (P × M)) (hG : IsOpen G) (hGR : G ⊆ incrementsOriginalParameterRegion Data)
    (hKG : Data.parameterSet ×ˢ (univ : Set M) ⊆ G)
    (input : Bool → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hInput : ∀ q a, ∃ UI : Set (Fin (m+1+d) → ℝ), IsOpen UI ∧
      incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input q) a) UI)
    (hSymm : ∀ q p, p ∈ Data.parameterOpen → ∀ x, (input q p x).IsSymm)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (n length j Rsub Lprimary : ℕ) (horder : j+1 ≤ n)
    (ell tau packet Minput Delta reserve c cT Bnative Bforward Meta : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hDelta : 0 ≤ Delta) (hReservePos : 0 < reserve) (hMeta : 0 ≤ Meta) (hBforward : 0 ≤ Bforward)
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
    (hReserve : ∀ q nu z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      reserve ≤ Data.linearArgument nu z.1 z.2 (input q z.1 z.2))
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hcT : 0 < cT) (hBnative : 0 < Bnative)
    (hnative : ∀ nu beta z, z ∈ (b nu beta).source → ‖fderiv ℝ (b nu beta) z‖ ≤ Bnative)
    (hTreserve : ∀ nu beta z, z ∈ (b nu beta).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e nu beta z.1).symm z.2 v‖^2)
    (Tinv : ℕ → ℝ) (hTinv : ∀ k, 0 ≤ Tinv k) (observer : Fin Data.atlas.count) :
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
    (prim : ∀ q, ParameterRound2GlobalMeanPrimitives F hF g (Ainput q) W primary) →
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
        reserve Bnd Mg Tobs F hF g (Ainput true) (Ainput false) W primary obs O S tau ell (Dinput*Delta)) := by
  intro F hF g0 W hW g Ainput primary obs oi a kappa O S Omega U R Rloc Sloc
    prim hsample hinvjet hForward hEtaProduced hEtaCount hPrimaryCount Cmap Mg Clocal Cobs Dlocal Dobs Dinput
    CutLocal NormalLocal CutObs NormalObs GradObs Bnd Tobs
  have hpacket0 : 0 ≤ packet := ENNReal.toReal_nonneg.trans hPacket
  have hMinput0 : 0 ≤ Minput := ENNReal.toReal_nonneg.trans (hMinput true)
  have hDlocal : 0 ≤ Dlocal := by dsimp only [Dlocal]; positivity
  have hDobs : 0 ≤ Dobs := by dsimp only [Dobs]; positivity
  have hDinput0 : 0 ≤ Dinput := add_nonneg hDlocal hDobs
  have hDinputM : 0 ≤ Dinput*Minput := mul_nonneg hDinput0 hMinput0
  have hBnd0 : 0 ≤ Bnd := by dsimp only [Bnd]; positivity
  have hMg0 : 0 ≤ Mg := actualAdaptedUniformGeometryCost_nonneg _ _ _ _ _ _ _ _ _
  have hCoreLe := actualOriginalGivenInputProfile_core_le Data n ell
  have hCore : incrementsOriginalCoreInputProfile Data n ell ≠ ⊤ := ne_top_of_le_ne_top hGiven hCoreLe
  have hCoreB : (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ packet :=
    (ENNReal.toReal_mono hGiven hCoreLe).trans hPacket
  have hLinearLe := actualOriginalGivenInputProfile_linear_le Data n ell
  have hLinearFinite : incrementsOriginalInputProfileWithLinear Data n ell ≠ ⊤ :=
    ne_top_of_le_ne_top hGiven hLinearLe
  have hLinearB : (incrementsOriginalInputProfileWithLinear Data n ell).toReal ≤ packet :=
    (ENNReal.toReal_mono hGiven hLinearLe).trans hPacket
  have hObsInv := contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem observer)
  have hSO : S ⊆ O := by
    intro z hz
    have hprod : (incrementsOriginalParameterPoint (a z),incrementsOriginalSourcePoint (a z)) = z := a.symm_apply_apply z
    have hpz : z.1 ∈ (Data.parameterChart i.2).target := (congrArg Prod.fst hprod) ▸ hz.1.2
    have hxz : z.2 ∈ obs.target := (congrArg Prod.snd hprod) ▸ hz.1.1
    have hpk := (actualOriginalNativeMap_evaluation_members Data oi hz).2
    exact ⟨⟨mem_univ _,hxz⟩,⟨hpz,mem_univ _⟩,hKG ⟨hpk,mem_univ _⟩⟩
  have dom := actual_raw_observer_domains F hF g (Ainput true) W primary (prim true) obs hObsInv S hSO
  have hSloc (nu) (beta) : Sloc nu beta ⊆ (g.chart nu beta).target := (dom.2.2.2.2 nu beta).2.2.2.2.1
  have hSlocBase (nu) (beta) : Sloc nu beta ⊆ (g0.chart nu beta).target := fun _ hz => (hSloc nu beta hz).1
  have hSlocB (nu) (beta) : Sloc nu beta ⊆ (b nu beta).target := by
    rw [← (hdata nu beta).1]
    exact hSlocBase nu beta
  have hOmegaCore (nu) : Omega nu ⊆ actualOriginalPrimaryNativeOpen Data nu oi := by
    intro z hz
    have hdif := original_native_differentiation Data oi z hz.1.2.1.1 hz.1.1.2
    refine ⟨⟨hdif,?_⟩,?_⟩
    · simp only [mem_preimage]
      rw [actual_original_jointPoint_native]
      exact hz.2.2
    · simp only [mem_preimage]
      rw [actual_original_jointPoint_native]
      exact hGR hz.1.2.2
  have hObsSample (nu) (z : X) (hz : z ∈ R nu) : a z ∈ incrementsOriginalPrimaryEvaluation Data nu oi :=
    ⟨hz.1,(hOmegaCore nu ((dom.2.2.2.1 nu).2.1 hz)).1.2⟩
  have hgeom (nu) (beta) := actualOriginalPrimaryFamily_native_geometry_profiles Tinv hTinv n
    Data hd hs hn i host b e hdata eta hactive hImm nu beta (Sloc nu beta) (hSlocB nu beta)
    (hsource nu beta) (hsample nu beta) ell packet c cT Bnative hell hell1 hEll
    hcT hBnative hCore hCoreB (hnative nu beta) (hTreserve nu beta) (hinvjet nu beta)
  have hfields (nu) (beta) := actualOriginalPrimaryFamily_cutoff_normal_profiles Tinv hTinv n
    Data hd hs hn i host b e hdata eta hactive nu beta (Sloc nu beta) (hSlocB nu beta)
    (hsource nu beta) (hsample nu beta) ell packet hell hCore hCoreB
    (fun k hk hkn => hinvjet nu beta k hk (by omega))
  have hobsfields (nu) := And.intro
    (actual_original_core_cutoff_native_jets Data hd hs nu n ell hell hCore packet hCoreB oi)
    (actual_original_core_normal_native_jets Data hd hs nu n ell hell hCore packet hCoreB oi)
  have hLocalArg (q) (nu) (beta) := parameterRound2_original_host_argument_germ_profiles Tinv hTinv n
    Data hd hLinear (input q) (hInput q) (hSymm q) (host nu beta,i.2) nu (b nu beta) (e nu beta)
    (hdata nu beta) (Sloc nu beta) (hSlocB nu beta) (hsource nu beta) (hsample nu beta)
    (fun w hw => (hactive nu beta w hw).1) ell packet Minput hell hLinearFinite hLinearB
    (hInputFinite q) (hMinput q) (fun k hk hkn => hinvjet nu beta k hk (by omega))
  have hLocalDiff (nu) (beta) := parameterRound2_original_host_argument_difference_germ_profiles Tinv hTinv n
    Data hd hLinear (input true) (input false) (hInput true) (hInput false) (hSymm true) (hSymm false)
    (host nu beta,i.2) nu (b nu beta) (e nu beta) (hdata nu beta) (Sloc nu beta) (hSlocB nu beta)
    (hsource nu beta) (hsample nu beta) (fun w hw => (hactive nu beta w hw).1)
    ell packet Delta hell hLinearFinite hLinearB hDiffFinite hDinput
    (fun k hk hkn => hinvjet nu beta k hk (by omega))
  have hObsArg (q) (nu) := parameterRound2_original_observer_argument_germ_profiles Data hd hLinear
    (input q) (hInput q) (hSymm q) n ell packet Minput hell hLinearFinite hLinearB
    (hInputFinite q) (hMinput q) nu oi
  have hObsDiff (nu) := parameterRound2_original_observer_argument_difference_germ_profiles Data hd hLinear
    (input true) (input false) (hInput true) (hInput false) (hSymm true) (hSymm false)
    n ell packet Delta hell hLinearFinite hLinearB hDiffFinite hDinput nu oi
  have hRlocU (nu) (beta) : Rloc nu beta ⊆ U nu beta := by
    intro z hz
    exact (dom.2.2.2.2 nu beta).2.1 ⟨(dom.2.2.2.1 nu).2.1 hz.1,hz.2⟩
  have hOverlap (nu) (beta) : U nu beta ⊆
      actualOriginalNativeGivenTransitionDomain Data (oi,(host nu beta,i.2)) := by
    intro z hz
    refine ⟨original_native_differentiation Data oi z hz.1.2.1.1 hz.1.1.2,?_⟩
    simp only [mem_preimage, Prod.fst, Prod.snd]
    rw [actual_original_jointPoint_native]
    exact ⟨(Data.parameterChart i.2).map_target hz.1.2.1.1,hz.2.1.1.2⟩
  have hObserver (nu) (beta) := actual_original_observer_adapted_positive_jets Data hd oi (host nu beta)
    (b nu beta) ((actual_host_slice_geometry_inputs _ (hd.atlas_smooth.chart_mem (host nu beta))
      _ _ _ (hdata nu beta)).2.1)
    (U nu beta) (Rloc nu beta) (dom.2.2.2.2 nu beta).1 (hRlocU nu beta) (hOverlap nu beta)
    (fun z hz => hz.2.1.2) (fun z hz => ⟨hz.1.1,hOverlap nu beta (hRlocU nu beta hz)⟩)
    n ell packet Bforward hell hBforward hGiven hPacket (hForward nu beta)
  have hBnd : 1 ≤ Bnd ∧ Mg ≤ Bnd ∧ CutLocal ≤ Bnd ∧ NormalLocal ≤ Bnd ∧
      CutObs ≤ Bnd ∧ NormalObs ≤ Bnd ∧ Meta ≤ Bnd ∧ GradObs ≤ Bnd ∧ Dinput*Minput ≤ Bnd := by
    have h1 := le_abs_self Mg
    have h2 := le_abs_self CutLocal
    have h3 := le_abs_self NormalLocal
    have h4 := le_abs_self CutObs
    have h5 := le_abs_self NormalObs
    have h6 := le_abs_self Meta
    have h7 := le_abs_self GradObs
    have ha1 := abs_nonneg Mg
    have ha2 := abs_nonneg CutLocal
    have ha3 := abs_nonneg NormalLocal
    have ha4 := abs_nonneg CutObs
    have ha5 := abs_nonneg NormalObs
    have ha6 := abs_nonneg Meta
    have ha7 := abs_nonneg GradObs
    dsimp only [Bnd]
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> linarith
  let Ascalar := fun q nu beta => parameterRound2_scalarPrimaryArgument F g (Ainput q) nu beta
  let Aobs := fun q nu => fun z : X => g.linearArgument nu z.1 (obs.symm z.2) (Ainput q z.1 (obs.symm z.2))
  have hAscalar (q) (nu) (beta) : ContDiffOn ℝ ∞ (Ascalar q nu beta) (g.chart nu beta).target :=
    parameterRound2_scalarPrimaryArgument_contDiffOn F g (Ainput q) W primary nu beta
      ((prim q).hSourceW nu beta) ((prim q).hChartInv nu beta) ((prim q).hInverse nu beta)
      ((prim q).hArgument nu)
  have hkappa : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ kappa (univ ×ˢ obs.target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (hObsInv.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have hkappaOmega (nu) : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ kappa (Omega nu) :=
    hkappa.mono (fun _ hz => hz.1.1)
  have hAobs (q) (nu) : ContDiffOn ℝ ∞ (Aobs q nu) (Omega nu) :=
    (((prim q).hArgument nu).comp (hkappaOmega nu) (dom.2.2.2.1 nu).2.2.2).contDiffOn
  have hEtaLocal (nu) (beta) : ContDiffOn ℝ ∞
      (fun z : X => g.eta nu beta (z.1,g.inverse nu beta z.1 z.2)) (g.chart nu beta).target := by
    have hh := (((prim true).hEta nu beta).comp ((prim true).hChartInv nu beta)
      (fun z hz => ((prim true).hSourceW nu beta ((g.chart nu beta).map_target hz)).1)).contDiffOn
    apply hh.congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [(prim true).hInverse nu beta z hz]
  have hEtaBound (nu) (beta) (k : ℕ) (hk : k ≤ n) (z : X) (hz : z ∈ Sloc nu beta) :
      ell^k*‖iteratedFDeriv ℝ k (fun w : X => g.eta nu beta (w.1,g.inverse nu beta w.1 w.2)) z‖ ≤ Meta := by
    have heq : (fun w : X => g.eta nu beta (w.1,g.inverse nu beta w.1 w.2)) =ᶠ[𝓝 z]
        eta nu beta ∘ (g0.chart nu beta).symm := by
      filter_upwards [(g0.chart nu beta).open_target.mem_nhds (hSlocBase nu beta hz)] with w hw
      rw [Function.comp_apply,actualOriginalPrimaryFamily_inverse Data hd hs hn i host b e hdata eta hactive nu beta w hw]
      rfl
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hEtaProduced nu beta k hk z hz
  have hArgBound (q) (nu) (beta) (k : ℕ) (hk : k ≤ n) (z : X) (hz : z ∈ Sloc nu beta) :
      ell^k*‖iteratedFDeriv ℝ k (Ascalar q nu beta) z‖ ≤ Dinput*Minput := by
    obtain ⟨V0,hV0,hSV0,hV0T,hreg,hbound⟩ := hLocalArg q nu beta
    have hh := hbound k hk z hz
    have hc : 2^n*(‖actualOriginalCoefficientFunctional (m+1)‖*Clocal*packet)*(Clocal*Minput) = Dlocal*Minput := by
      dsimp only [Dlocal]
      ring
    rw [hc] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hDobs) hMinput0)
  have hArgDiff (nu) (beta) (k : ℕ) (hk : k ≤ n) (z : X) (hz : z ∈ Sloc nu beta) :
      ell^k*‖iteratedFDeriv ℝ k (fun w => Ascalar true nu beta w-Ascalar false nu beta w) z‖ ≤ Dinput*Delta := by
    obtain ⟨V0,hV0,hSV0,hV0T,hreg,hbound⟩ := hLocalDiff nu beta
    have hh := hbound k hk z hz
    have hc : 2^n*(‖actualOriginalCoefficientFunctional (m+1)‖*Clocal*packet)*(Clocal*Delta) = Dlocal*Delta := by
      dsimp only [Dlocal]
      ring
    rw [hc] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hDobs) hDelta)
  have hObsArgBound (q) (nu) (k : ℕ) (hk : k ≤ n) (z : X) (hz : z ∈ R nu) :
      ell^k*‖iteratedFDeriv ℝ k (Aobs q nu) z‖ ≤ Dinput*Minput := by
    obtain ⟨V0,hV0,hSV0,hV0T,hreg,hbound⟩ := hObsArg q nu
    have hh := hbound k hk z (hObsSample nu z hz)
    have hc : 2^n*(‖actualOriginalCoefficientFunctional (m+1)‖*Cobs*packet)*(Cobs*Minput) = Dobs*Minput := by
      dsimp only [Dobs]
      ring
    rw [hc] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hDlocal) hMinput0)
  have hObsArgDiff (nu) (k : ℕ) (hk : k ≤ n) (z : X) (hz : z ∈ R nu) :
      ell^k*‖iteratedFDeriv ℝ k (fun w => Aobs true nu w-Aobs false nu w) z‖ ≤ Dinput*Delta := by
    obtain ⟨V0,hV0,hSV0,hV0T,hreg,hbound⟩ := hObsDiff nu
    have hh := hbound k hk z (hObsSample nu z hz)
    have hc : 2^n*(‖actualOriginalCoefficientFunctional (m+1)‖*Cobs*packet)*(Cobs*Delta) = Dobs*Delta := by
      dsimp only [Dobs]
      ring
    rw [hc] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hDlocal) hDelta)
  have hPullSupport (nu) := actual_original_parameter_pullback_support Data i.2 W
    (fun z hz => hz.1.1) (fun z hz => hGR hz.2) nu
  have hReserveNative (q) (nu) (w : Ep × M)
      (hw : w ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)) :
      reserve ≤ g.linearArgument nu w.1 w.2 (Ainput q w.1 w.2) := by
    have hWw : w ∈ W := by rcases hw with ⟨v,hv,rfl⟩; exact v.property
    exact hReserve q nu _ hWw.2 (hPullSupport nu w hw)
  refine ⟨hBnd0,hMg0,hDinput0,⟨{
    prim := prim true
    primbar := prim false
    hO := dom.1
    hSO := hSO
    hkappaO := dom.2.1
    hmapWO := dom.2.2.1
    Omega := Omega
    U := U
    Sloc := Sloc
    hOmega := fun nu => (dom.2.2.2.1 nu).1
    hSOmega := fun nu => (dom.2.2.2.1 nu).2.1
    hkappa := fun nu => (dom.2.2.2.1 nu).2.2.1
    hmapW := fun nu z hz => ((dom.2.2.2.1 nu).2.2.2 hz).1
    hU := fun nu beta => (dom.2.2.2.2 nu beta).1
    hOU := fun nu beta => (dom.2.2.2.2 nu beta).2.1
    hSloc := hSloc
    hsource := fun nu beta => (dom.2.2.2.2 nu beta).2.2.1
    hphi := fun nu beta => (dom.2.2.2.2 nu beta).2.2.2.1
    hmap := fun nu beta => (dom.2.2.2.2 nu beta).2.2.2.2.2.1
    htau := htau
    htaul := htaul
    hell1 := hell1
    hDelta := mul_nonneg hDinput0 hDelta
    L := fun _ _ => parameterRound2_scalarArgumentIdentity
    A := Ascalar true
    Abar := Ascalar false
    hL := fun nu beta => (parameterRound2_scalarArgumentIdentity_profiles (g.chart nu beta).target ell).1
    hInput := hAscalar true
    hInputbar := hAscalar false
    hRep := fun nu beta z hz => rfl
    hRepbar := fun nu beta z hz => rfl
    hCut := fun nu beta => (hfields nu beta).1.1.mono (fun _ hz => hz.1)
    hEta := hEtaLocal
    hNormal := fun nu beta => (hfields nu beta).2.1.mono (fun _ hz => hz.1)
    hBR := (prim true).hSecond
    hReserve := fun nu beta z hz =>
      ⟨hReserveNative true nu _ ((dom.2.2.2.2 nu beta).2.2.2.2.2.2 z hz),
       hReserveNative false nu _ ((dom.2.2.2.2 nu beta).2.2.2.2.2.2 z hz)⟩
    hBRb := fun nu beta k hk z hz => ((hgeom nu beta).2.2.2.2.2.1.2 k hk z hz).trans hBnd.2.1
    hLb := fun nu beta k hk z hz =>
      ((parameterRound2_scalarArgumentIdentity_profiles (g.chart nu beta).target ell).2 k z).trans hBnd.1
    hInputb := fun nu beta k hk z hz => (hArgBound true nu beta k hk z hz).trans hBnd.2.2.2.2.2.2.2.2
    hInputbarb := fun nu beta k hk z hz => (hArgBound false nu beta k hk z hz).trans hBnd.2.2.2.2.2.2.2.2
    hCutb := fun nu beta k hk z hz => ((hfields nu beta).1.2 k hk z hz).trans hBnd.2.2.1
    hEtab := fun nu beta k hk z hz => (hEtaBound nu beta k hk z hz).trans hBnd.2.2.2.2.2.2.1
    hNormalb := fun nu beta k hk z hz => ((hfields nu beta).2.2 k hk z hz).trans hBnd.2.2.2.1
    hDiff := hArgDiff
    hAb := fun nu beta => (hgeom nu beta).2.2.2.2.2.2.1.2
    hBb := fun nu beta => (hgeom nu beta).2.2.2.2.2.2.2.2
    hGb := fun nu beta k hk => (hgeom nu beta).2.2.1.2 k (hk.trans horder)
    hJb := fun nu beta k hk => (hgeom nu beta).2.2.2.1.2 k (hk.trans horder)
    hTb := fun nu beta k hk => (hgeom nu beta).2.2.2.2.1.2 k (hk.trans horder)
    hphib := fun nu beta k hk hkj => (hObserver nu beta).2 k hk (by omega)
    hRsub := ?_
    Lobs := fun _ => parameterRound2_scalarArgumentIdentity
    Aobs := Aobs true
    Abarobs := Aobs false
    hLobs := fun nu => (parameterRound2_scalarArgumentIdentity_profiles (Omega nu) ell).1
    hAobs := hAobs true
    hAbarobs := hAobs false
    hRepobs := fun nu z hz => rfl
    hRepbarobs := fun nu z hz => rfl
    hCutobs := fun nu => (hobsfields nu).1.1.mono (hOmegaCore nu)
    hNormalobs := fun nu => (hobsfields nu).2.1.mono (hOmegaCore nu)
    hPhaseobs := fun nu => (((prim true).hPhase nu).comp (hkappaOmega nu)
      (dom.2.2.2.1 nu).2.2.2).contDiffOn
    hReserveobs := fun nu z hz => ⟨hReserveNative true nu _ hz.2,hReserveNative false nu _ hz.2⟩
    hLobsb := fun nu k hk z hz =>
      ((parameterRound2_scalarArgumentIdentity_profiles (Omega nu) ell).2 k z).trans hBnd.1
    hAobsb := fun nu k hk z hz => (hObsArgBound true nu k (hk.trans horder) z hz).trans hBnd.2.2.2.2.2.2.2.2
    hAbarobsb := fun nu k hk z hz => (hObsArgBound false nu k (hk.trans horder) z hz).trans hBnd.2.2.2.2.2.2.2.2
    hCutobsb := fun nu k hk z hz => ((hobsfields nu).1.2 k (hk.trans horder) z (hObsSample nu z hz)).trans hBnd.2.2.2.2.1
    hNormalobsb := fun nu k hk z hz => ((hobsfields nu).2.2 k (hk.trans horder) z (hObsSample nu z hz)).trans hBnd.2.2.2.2.2.1
    hGradobsb := fun nu r k hk z hz => (actual_original_observer_phase_spatial_jets Data hd hs n ell packet hell
      hGiven hPacket nu oi r k (by omega) z (hObsSample nu z hz)).trans hBnd.2.2.2.2.2.2.2.1
    hDiffobs := fun nu k hk => hObsArgDiff nu k (hk.trans horder)
    hCover := fun nu z hz => ⟨hz.1,(prim true).hPrimarySupport nu hz.2⟩
    hPositiveCover := fun nu z hz => ⟨(prim true).hPositive nu (kappa z) hz.2,(prim false).hPositive nu (kappa z) hz.2⟩
    hCount := fun z hz => hPrimaryCount _ (dom.2.2.1 (hSO hz)) }⟩⟩
  intro nu z hz
  apply (Finset.card_le_card ?_).trans (hEtaCount nu _ (dom.2.2.1 (hSO hz.1)))
  intro beta hb
  have hp := (Finset.mem_filter.mp hb).2
  obtain ⟨w,hw,heq⟩ := hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨w,tsupport_mul_subset_left hw,heq⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualOriginalPrimaryFamily_native_raw_profiles_from_primitives
