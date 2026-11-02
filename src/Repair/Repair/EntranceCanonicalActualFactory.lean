import Repair.EntranceCanonicalFactoryPlanned

/-!
# The actual original factory reaches the full repair endpoint

Both primary and nonlinear signed secondary packets, every reference
reserve, all chart profiles, the literal raw increment, the initial state
and the same natural-time trajectory are manufactured inside this theorem.
The displayed fixed plan reads only three finite reference prefixes. Its
numerical parameters and profiles have no atlas or reference-map argument.
`rhoRaw` defines the positive reference neighborhood; `rhoReserve` is the
weighted decomposition reserve and is deliberately a separate quantity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle Metric
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
universe uM uP
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
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

theorem repairEntranceCanonical_actual_factory_planned_repair
    (b : RepairReferenceFactoryBudget m d N)
    (T B0 Bp Bs lower rhoRaw rhoReserve C2 C442 tolerance : ℝ)
    (labelBound Ds Dp Lprimary : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (BS TS BP TP Parent Parameter Spatial allowedGiven allowedReference allowedEnvelope : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j)
    (hParent : ∀ j, 0 ≤ Parent j) (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (hAllowedReference : ∀ j, 0 ≤ allowedReference j) (hAllowedEnvelope : ∀ j, 0 ≤ allowedEnvelope j)
    (hT : 0 < T) (hB0 : 0 ≤ B0) (hBp : 0 ≤ Bp) (hBs : 0 ≤ Bs)
    (hRadius : 0 ≤ b.modelRadius) (hLower : 0 < lower) (hReservePositive : 0 < rhoReserve)
    (hC2 : 0 ≤ C2) (hC442 : 0 ≤ C442) (hTolerance : 0 < tolerance)
    (hTbound : Spatial 1 ≤ T) :
    let fixed := repairEntranceFactoryProfiles b T B0 Bp Bs labelBound Ds Dp
      BS TS BP TP Parent Parameter Spatial allowedGiven allowedReference allowedEnvelope
      hBS hTS hBP hTP hAllowedReference hAllowedEnvelope
    let parameters := repairEntranceFactoryParameters b T B0 Bp Bs lower rhoReserve C2 (allowedGiven 0)
      tolerance labelBound Ds Dp Lprimary radius hradius Parameter Spatial hT hB0 hBp hBs hRadius
      hLower hReservePositive hC2 hTolerance hParameter hSpatial
    ∀ (seed : RepairOriginalReferenceSeed (m+1) d N M P)
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
      (hCenter : ∀ i, ‖center i‖ ≤ B0)
      (hParameterValue : ∀ ip p, p ∈ seed.parameterNormDomain ip → ‖p‖ ≤ Bp)
      (hSourceValue : ∀ i x, x ∈ seed.sourceNormDomain i → ‖x‖ ≤ Bs)
      (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
      (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
      (hLabel : ∀ nu, label nu ≤ labelBound)
      (hProper : ∀ nu mu, nu ≠ mu →
        (tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff nu) ∩
          tsupport ((repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).cutoff mu)).Nonempty →
          label nu ≠ label mu),
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let weight := fun nu => repairReferenceSignedHierarchy b.cover b.operatorBound T ^ label nu
    let Ref := repairReferenceWeightedData (repairReferencePositiveData raw rhoRaw) weight
    ∀ (reference Given envelope : ℕ → ℝ)
      (smoothing : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp radius hradius reference Given)
      (hReferenceMap : Ref.F=smoothing.referenceMap)
      (hNormSource : Ref.sourceNormDomain=smoothing.Omega)
      (hNormParameter : Ref.parameterNormDomain=smoothing.Q)
      (hAll : Ref.parameterSet=univ)
      (hs : IncrementsOriginalSmoothInputs Ref)
      (hp : IncrementsOriginalPhaseConditions Ref smoothing.domain hs)
      (hn : IncrementsOriginalFreeNormalConditions Ref smoothing.domain hs)
      (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Ref)
      (hLinear : IncrementsOriginalLinearSmoothInputs Ref)
      (hLocal : ∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (Ref.cutoff nu))).card ≤ Lprimary)
      (hImm : IncrementsOriginalSliceImmersionInputs Ref)
      (hEll : IncrementsOriginalCoordinateEllipticityInputs Ref lower)
      (hReserve : IncrementsOriginalDecompositionReserveInputs Ref rhoReserve)
      (transition : RepairOriginalTransitionBudgets Ref Parameter Spatial)
      (hMap2 : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
        smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
        smoothing.closedSamples).toReal ≤ C2)
      (hMap442 : (paperAtlasCj 442 (incrementsOriginalMapCoordinates Ref.atlas smoothing.parameterFamily.chart
        smoothing.referenceMap) (incrementsOriginalDifferentiation Ref.atlas smoothing.parameterFamily.chart)
        smoothing.closedSamples).toReal ≤ C442)
      (hEnvelope : ∀ j, smoothing.closedReferenceProfile j ≤ envelope j)
      (hGivenPrefix : ∀ j, j ≤ repairEntrancePrimitiveDepth → allowedGiven j=Given j)
      (hReferencePrefix : ∀ j, j ≤ repairEntrancePrimitiveDepth → allowedReference j=reference j)
      (hEnvelopePrefix : ∀ j, j ≤ repairEntrancePrimitiveDepth → allowedEnvelope j=envelope j),
    let theta := round3ParameterProductParent Ref.atlas smoothing.parameterFamily
      (squareNormalizedCutoff smoothing.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff smoothing.parameterPreparation.raw)
    ∀ (hThetaCompact : ∀ i, IsCompact (tsupport (theta i)))
      (hThetaSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
      (hThetaSource : ∀ i, tsupport (theta i) ⊆
        ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
        ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i)
      (hPart : ∀ z, ∑ i, theta i z=1)
      (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1))
      (hParentJets : ∀ parent i j z, parameterTensorModelEquiv (m+1) d z ∈
        incrementsOriginalEvaluation seed.atlas seed.parameterChart seed.sourceNormDomain
          seed.parameterNormDomain seed.parameterSet i →
        ‖iteratedFDeriv ℝ j (theta parent ∘
          ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm) z‖ ≤ Parent j),
    RepairEntranceCanonicalPlannedLimit Ref smoothing parameters fixed C2 C442 tolerance := by
  intro fixed parameters seed hF Htensor S O K center family hseed hSO hSample hSEval hO hK hBuffer
    hInner hCenter hParameterValue hSourceValue outer label hLabel hProper raw weight Ref
    reference Given envelope smoothing hReferenceMap hNormSource hNormParameter hAll hs hp hn hDecomp
    hLinear hLocal hImm hEll hReserve transition hMap2 hMap442 hEnvelope hGivenPrefix hReferencePrefix
    hEnvelopePrefix theta hThetaCompact hThetaSmooth hThetaSource hPart hCount hParentJets
  have hSamples := smoothing.originalSamples_eq_closed hAll hNormSource hNormParameter
  have hCompact : ∀ i, IsCompact (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i) := by
    intro i
    rw [hSamples]
    exact smoothing.closedSamples_compact i
  have hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet)).toReal ≤ C2 := by
    simpa only [smoothing.chart_eq,← hReferenceMap,← hSamples] using hMap2
  have hJoint : ContMDiff IJ 𝓘(ℝ,Ey) ∞ Ref.F := by
    rw [hReferenceMap]
    simpa only [modelWithCornersSelf_prod] using smoothing.referenceMap_smooth
  obtain ⟨a⟩ := repairEntrance_actual_factory_assembly b seed hF Htensor S O K center family hseed
    hSO hSample hSEval hO hK hBuffer hInner outer theta hThetaCompact hThetaSmooth hThetaSource
    rhoRaw T B0 Bp Bs lower C2 hT hB0 hBp hBs hRadius hLower hC2 hCenter labelBound label hLabel hProper
    Parent Parameter Spatial hParent hParameter hSpatial hTbound hParameterValue hSourceValue hParentJets
    smoothing.domain hs hn hAll hJoint transition hEll hCompact hMap
  have hPrefix := repairEntranceFactoryProfiles_reference_prefix b T B0 Bp Bs labelBound Ds Dp
    repairEntrancePrimitiveDepth BS TS BP TP Parent Parameter Spatial
    allowedGiven allowedReference allowedEnvelope Given reference envelope
    hBS hTS hBP hTP hAllowedReference hAllowedEnvelope
    (fun j => ENNReal.toReal_nonneg.trans (smoothing.reference_bound j))
    (fun j => ENNReal.toReal_nonneg.trans (hEnvelope j)) hGivenPrefix hReferencePrefix hEnvelopePrefix
  exact repairEntranceCanonical_factory_assembled_planned_limit fixed Ref BS TS BP TP hBS hTS hBP hTP
    Ds Dp radius hradius reference Given smoothing hReferenceMap hNormSource hNormParameter hAll
    hs hp hn hDecomp hLinear Lprimary hLocal hImm lower hEll rhoReserve hReserve tolerance hTolerance
    C2 C442 hC2 hC442 hMap2 hMap442 envelope hEnvelope _ _ _ _ _ _ _ _ a hPart hCount
    (fun i z hz => ⟨(hThetaSource i hz).1.1,mem_univ _⟩) hPrefix

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_actual_factory_planned_repair
