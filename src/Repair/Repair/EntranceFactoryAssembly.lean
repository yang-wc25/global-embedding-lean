import Repair.EntranceFactoryNumericalPlan

/-! Actual primary and nonlinear secondary factories, with their common
pure numerical plan. This is a constructed internal certificate; the
public repair endpoint manufactures it from the original geometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Metric
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

structure RepairEntranceFactoryAssembly
    (data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
    (hn : IncrementsOriginalFreeNormalConditions data hd hs)
    (theta : (Fin data.atlas.count × Fin data.parameterCount) → P × M → ℝ)
    (primaryNumbers secondaryNumbers : RepairEntranceFrameNumbers m d N)
    (Forward Inverse Meta secondaryForward secondaryInverse : ℕ → ℝ)
    (secondaryCutoff : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ) where
  primary : Round3ParameterWholePrimaryPieceSupply data theta
  profiles : Round3ParameterWholeReferenceProfiles data hd hs theta primary
  observer : RepairPrimaryObserverBudget data hd hs theta primary profiles
  secondary : Round3PreparedParameterSecondaryPacket data hd hs theta
  numeric : IncrementSecondaryReferenceBudget data hd hs theta secondary
  charts : IncrementSecondaryChartBudget data hd hs theta secondary
  primary_cF : profiles.cF=primaryNumbers.cF
  primary_cT : profiles.cT=primaryNumbers.cT
  primary_MH : profiles.MH=primaryNumbers.MH
  primary_inverse : profiles.Tinv=primaryNumbers.inverse
  primary_forward : observer.forwardProfile=Forward
  primary_observer_inverse : observer.inverseProfile=Inverse
  secondary_cF : numeric.cF=secondaryNumbers.cF
  secondary_cT : numeric.cT=secondaryNumbers.cT
  secondary_MH : numeric.MH=secondaryNumbers.MH
  secondary_inverse : numeric.nativeInverse=secondaryNumbers.inverse
  secondary_forward : charts.forwardProfile=secondaryForward
  secondary_observer_inverse : charts.inverseProfile=secondaryInverse
  secondary_cutoff : charts.cutoffProfile=secondaryCutoff
  meta_nonneg : ∀ j, 0 ≤ Meta j
  primary_parameter : ∀ nu i a y, y ∈ tsupport (primary.piece nu i a).cutoff →
    y.1 ∈ data.parameterNormDomain i.2
  secondary_parameter : ∀ r i a y, y ∈ (secondary.piece r i a).carrier →
    y.1 ∈ data.parameterNormDomain i.2
  cutoff : RepairOriginalPrimaryCutoffJets data
    (round3ParameterWholePrimaryFamily data hd hs hn theta
      (round3OuterReferencePrimaryPacket data hd hs theta primary profiles)) Meta

 theorem RepairEntranceFactoryAssembly.primary_tolerance
    {data : IncrementsOriginalNativeData (m+1) d N M P}
    {hd : IncrementsOriginalDomainConditions data} {hs : IncrementsOriginalSmoothInputs data}
    {hn : IncrementsOriginalFreeNormalConditions data hd hs}
    {theta : (Fin data.atlas.count × Fin data.parameterCount) → P × M → ℝ}
    {p s : RepairEntranceFrameNumbers m d N}
    {FC IC MC SF SI : ℕ → ℝ} {SC : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ}
    (a : RepairEntranceFactoryAssembly data hd hs hn theta p s FC IC MC SF SI SC) :
    repairEntranceGeometryTolerance m d N a.profiles.Tinv a.profiles.cF a.profiles.cT a.profiles.MH
      a.profiles.cF_pos a.profiles.cT_pos = p.tolerance := by
  simp only [a.primary_inverse,a.primary_cF,a.primary_cT,a.primary_MH,
    RepairEntranceFrameNumbers.tolerance]

 theorem RepairEntranceFactoryAssembly.secondary_tolerance
    {data : IncrementsOriginalNativeData (m+1) d N M P}
    {hd : IncrementsOriginalDomainConditions data} {hs : IncrementsOriginalSmoothInputs data}
    {hn : IncrementsOriginalFreeNormalConditions data hd hs}
    {theta : (Fin data.atlas.count × Fin data.parameterCount) → P × M → ℝ}
    {p s : RepairEntranceFrameNumbers m d N}
    {FC IC MC SF SI : ℕ → ℝ} {SC : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ}
    (a : RepairEntranceFactoryAssembly data hd hs hn theta p s FC IC MC SF SI SC) :
    incrementSecondaryStabilityTolerance a.numeric = s.tolerance := by
  simp only [incrementSecondaryStabilityTolerance,a.secondary_inverse,a.secondary_cF,
    a.secondary_cT,a.secondary_MH,RepairEntranceFrameNumbers.tolerance]

theorem repairEntrance_actual_factory_assembly
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,Ey) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (hO : ∀ i, IsOpen (O i))
    (hK : ∀ i, K i ⊆ closedBall (center i) b.modelRadius)
    (hBuffer : ∀ i z, z ∈ K i → ball z b.buffer ⊆ O i)
    (hInner : ∀ i z, z ∈ O i → (seed.atlas.chart i.1).symm z.2 ∈ seed.atlas.inner i.1)
    (outer theta : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hThetaCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hThetaSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i)
    (rho T B0 Bp Bs lower C2 : ℝ)
    (hT : 0 < T) (hB0 : 0 ≤ B0) (hBp : 0 ≤ Bp) (hBs : 0 ≤ Bs) (hRadius : 0 ≤ b.modelRadius)
    (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (hCenter : ∀ i, ‖center i‖ ≤ B0)
    (labelBound : ℕ) (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu, label nu ≤ labelBound)
    (hProper : ∀ nu mu, nu ≠ mu →
      (tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff nu) ∩
        tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff mu)).Nonempty →
        label nu ≠ label mu)
    (Parent Parameter Spatial : ℕ → ℝ)
    (hParent : ∀ j, 0 ≤ Parent j) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (hTbound : Spatial 1 ≤ T)
    (hParameterValue : ∀ ip p, p ∈ seed.parameterNormDomain ip → ‖p‖ ≤ Bp)
    (hSourceValue : ∀ i x, x ∈ seed.sourceNormDomain i → ‖x‖ ≤ Bs)
    (hParentJets : ∀ parent i j z, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation seed.atlas seed.parameterChart seed.sourceNormDomain
        seed.parameterNormDomain seed.parameterSet i →
      ‖iteratedFDeriv ℝ j (theta parent ∘
        ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm) z‖ ≤ Parent j) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let weight := fun nu => repairReferenceSignedHierarchy b.cover b.operatorBound T ^ label nu
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    let cap := repairEntranceFactoryWeightCap b T labelBound
    let p := repairEntranceFactoryPrimaryFrame b T Bp Bs lower C2 labelBound Spatial hT hBp hBs hLower hC2 hSpatial
    let s := repairEntranceFactorySecondaryFrame b T B0 Bs lower C2 labelBound Parameter Spatial
      hT hB0 hBs hRadius hLower hC2 hParameter hSpatial
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (hn : IncrementsOriginalFreeNormalConditions data hd hs)
      (hAll : data.parameterSet=univ) (hJoint : ContMDiff IJ 𝓘(ℝ,Ey) ∞ data.F)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial)
      (hEll : IncrementsOriginalCoordinateEllipticityInputs data lower)
      (hCompact : ∀ i, IsCompact (incrementsOriginalEvaluation data.atlas data.parameterChart
        data.sourceNormDomain data.parameterNormDomain data.parameterSet i))
      (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates data.atlas data.parameterChart data.F)
        (incrementsOriginalDifferentiation data.atlas data.parameterChart)
        (incrementsOriginalEvaluation data.atlas data.parameterChart data.sourceNormDomain
          data.parameterNormDomain data.parameterSet)).toReal ≤ C2),
    Nonempty (RepairEntranceFactoryAssembly data hd hs hn theta p s
      (repairEntranceFactoryForward b cap Bp Bs Parameter Spatial)
      (repairEntranceFactoryInverse b cap Bp Bs Parameter Spatial)
      (repairEntranceFactoryMeta b cap Bp Bs Parent Parameter Spatial)
      (repairEntranceOriginalForwardProfile Bp
        (repairEntranceFactorySecondaryForward b T B0 Bs labelBound Parameter Spatial) Parameter Spatial)
      (repairEntranceOriginalInverseProfile Bp Bs
        (repairEntranceFactorySecondaryInverse b T B0 Bs labelBound Parameter Spatial) Parameter Spatial)
      (incrementSecondaryCutoffProfile X (incrementFactorySignedMu b T)
        (incrementFactorySignedMb b T B0 Bs labelBound Parameter Spatial)
        (incrementFactorySignedBuffer b Parameter Spatial))) := by
  intro raw weight data cap p s hd hs hn hAll hJoint transition hEll hCompact hMap
  have hCap := repairEntranceFactoryWeightCap_one_le b T hT labelBound
  have hBase := (repairReferenceSignedHierarchy_gt_one b.cover b.operatorBound T hT.le).le
  have hWeight : ∀ nu, 1 ≤ weight nu := fun _ => one_le_pow₀ hBase
  have hWeightCap : ∀ nu, weight nu ≤ cap := fun nu => pow_le_pow_right₀ hBase (hLabel nu)
  obtain ⟨primary,profiles,observer,hPiece,hCF,hCT,hMH,hNI,hNF,hFC,hIC,hMeta,hPrimaryParam,hCutoff⟩ :=
    repairEntrance_actual_original_primary_factory b seed hF Htensor S O K center family hseed
      hSO hSample hSEval hO hInner outer theta hThetaCompact hThetaSmooth
      (fun i z hz => (hThetaSource i hz).1) (fun i z hz => (hThetaSource i hz).2)
      rho cap T Bp Bs lower C2 hCap hT hBp hBs hLower hC2 weight hWeight hWeightCap
      Parent Parameter Spatial hParent hParameter hSpatial hTbound hParameterValue hSourceValue hParentJets
      hd hs hn hAll hJoint transition hEll hCompact hMap
  have hCoords := parameterRound2_originalMapCoordinates_contDiffOn data.atlas data.parameterChart
    hd.atlas_smooth hd.parameter_charts_smooth data.F
    (by simpa only [modelWithCornersSelf_prod] using hJoint)
  have hMapFinite := parameterRound2_paperAtlasCj_finite_of_compact
    (incrementsOriginalMapCoordinates data.atlas data.parameterChart data.F)
    (incrementsOriginalDifferentiation data.atlas data.parameterChart)
    (incrementsOriginalEvaluation data.atlas data.parameterChart data.sourceNormDomain
      data.parameterNormDomain data.parameterSet)
    (parameterRound2_originalDifferentiation_open data.atlas data.parameterChart)
    hCompact (fun _ _ hz => hz.1) hCoords 2
  obtain ⟨secondary,numeric,charts,hSI,hSCF,hSCT,hSMH,hSF,hSIC,hSC,hSecondaryParam,hCard⟩ :=
    increment_actual_factory_secondary_geometry b seed hF Htensor S O K center family hseed outer
      hSample hSEval theta hThetaCompact hThetaSmooth hThetaSource hO hK hBuffer hInner
      B0 Bs hB0 hBs hRadius hCenter hSourceValue rho T hT labelBound label hLabel hProper
      hd hs hAll hJoint lower C2 hLower hC2 hEll hMapFinite hMap Parameter Spatial hParameter hSpatial
      transition hTbound Bp hBp hParameterValue
  exact ⟨{
    primary := primary, profiles := profiles, observer := observer
    secondary := secondary, numeric := numeric, charts := charts
    primary_cF := hCF, primary_cT := hCT, primary_MH := hMH, primary_inverse := hNI
    primary_forward := hFC, primary_observer_inverse := hIC
    secondary_cF := hSCF, secondary_cT := hSCT, secondary_MH := hSMH, secondary_inverse := hSI
    secondary_forward := hSF, secondary_observer_inverse := hSIC
    secondary_cutoff := funext fun BS => funext fun TS => funext fun BP => funext fun TP =>
      funext fun Ds => funext fun Dp => hSC BS TS BP TP Ds Dp
    meta_nonneg := hMeta, primary_parameter := hPrimaryParam, secondary_parameter := hSecondaryParam
    cutoff := hCutoff }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_factory_assembly
