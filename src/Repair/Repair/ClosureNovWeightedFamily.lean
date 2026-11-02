import Repair.IncrementWeightedRealization

/-! The same original weighted realization, assembled from the actual nonconvex
buffered factories. This intermediate keeps the existing native data, phase,
normal, decomposition and reserve definitions. ParentFactory supplies the
families without requiring a convex whole-chart domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal Classical
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
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance novWeightedFamilyProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance novWeightedFamilyTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance novWeightedFamilyProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M


def ClosureNovWeightedFamilyResult
    (b : RepairReferenceFactoryBudget m d N) (Ds Dp : ℕ)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x)
      S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (T : ℝ) (Parameter Spatial : ℕ → ℝ) : Prop :=
    let raw := repairReferenceOriginalFamilyData b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x)
      S O K center family hseed outer
    let positive := repairReferencePositiveData raw (repairReferenceFactoryPositiveReserve b)
    let labelBound := ((Ds+2)*(Dp+2))*(b.pieceBound*Fintype.card Edge)
    let base := repairReferenceSignedHierarchy b.cover b.operatorBound T
    let cap := base^labelBound
    ∃ label : Fin positive.primaryCount → ℕ,
      (∀ nu, label nu < labelBound) ∧
      (∀ nu mu, nu ≠ mu → (tsupport (positive.cutoff nu) ∩ tsupport (positive.cutoff mu)).Nonempty →
        label nu ≠ label mu) ∧
      let weight : Fin positive.primaryCount → ℝ := fun nu => base^label nu
      let data := repairReferenceWeightedData positive weight
      ∃ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
        IncrementsOriginalPhaseConditions data hd hs ∧
        IncrementsOriginalFreeNormalConditions data hd hs ∧
        IncrementsOriginalQualitativeDecompositionInputs data ∧
        IncrementsOriginalDecompositionReserveInputs data (repairReferenceFactoryPositiveReserve b/cap^2) ∧
        IncrementsOriginalLinearSmoothInputs data ∧
        (∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (data.cutoff nu))).card ≤ labelBound) ∧
        RepairOriginalTransitionBudgets data Parameter Spatial

/-- Actual phase, normal, decomposition, positive reserve, coefficient and
multiplicity preparation from the original allowed map class. The supplied actual local
family is retained and every label is constructed in this proof. The numerical label
bound and reserve contain no chart count. -/
theorem closureNov_original_weighted_family_realization
    (b : RepairReferenceFactoryBudget m d N) (Ds Dp : ℕ)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x)
      S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ seed.F0)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuterSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hOuterPartition : ∀ p ∈ seed.parameterOpen, ∀ x, ∑ i, outer i (p,x)^2=1)
    (hOuterCarrier : ∀ i, tsupport (outer i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
        ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i)
    (sourceSupport : Fin seed.atlas.count → Set M)
    (parameterSupport : Fin seed.parameterCount → Set P)
    (hDs : ∀ i, tensorEnlargedSupportDegree sourceSupport i ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree parameterSupport i ≤ Dp)
    (hOuterSupport : ∀ i, tsupport (outer i) ⊆ parameterSupport i.2 ×ˢ sourceSupport i.1)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (T : ℝ) (hT : 0 ≤ T) (Parameter Spatial : ℕ → ℝ) (hSpatial : Spatial 1 ≤ T)
    (hParameterTransitions : ∀ ip jp k, 1 ≤ k → ∀ z : X,
      z.1 ∈ seed.parameterNormDomain ip →
      z ∈ (((seed.parameterChart ip).symm.trans (seed.parameterChart jp)).prod
        (OpenPartialHomeomorph.refl D)).source →
      ‖iteratedFDeriv ℝ k (((seed.parameterChart ip).symm.trans (seed.parameterChart jp)).prod
        (OpenPartialHomeomorph.refl D)) z‖ ≤ Parameter k)
    (hSpatialTransitions : ∀ i j k, 1 ≤ k → ∀ z : X,
      z.2 ∈ seed.sourceNormDomain i →
      z ∈ (repairReferenceHostTransition (seed.atlas.chart i) (seed.atlas.chart j)).source →
      ‖iteratedFDeriv ℝ k (repairReferenceHostTransition (seed.atlas.chart i) (seed.atlas.chart j)) z‖ ≤ Spatial k) :
    ClosureNovWeightedFamilyResult b Ds Dp seed hF S O K center family hseed outer T Parameter Spatial := by
  classical
  unfold ClosureNovWeightedFamilyResult
  intro raw positive labelBound base cap
  obtain ⟨hd,hs,hn,hD,hr⟩ := repair_reference_original_family_positive b seed hF S
    O K center family hseed hFjoint hSO hSample outer hOuterSmooth hOuterPartition hOuterCarrier
  obtain ⟨label,hBound,hDistinct⟩ := repair_reference_original_family_labels b seed hF
    (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x) S
    O K center family hseed outer sourceSupport parameterSupport Ds Dp hDs hDp hOuterSupport
  have hBase : 1 < base := repairReferenceSignedHierarchy_gt_one b.cover b.operatorBound T hT
  let weight : Fin positive.primaryCount → ℝ := fun nu => base^label nu
  have hWeight (nu : Fin positive.primaryCount) : 0 < weight nu := pow_pos (zero_lt_one.trans hBase) _
  have hCap : 0 < cap := pow_pos (zero_lt_one.trans hBase) _
  have hWeightCap (nu : Fin positive.primaryCount) : weight nu ≤ cap :=
    pow_le_pow_right₀ hBase.le (hBound nu).le
  let data := repairReferenceWeightedData positive weight
  let hdW : IncrementsOriginalDomainConditions data := repairReferenceWeightedDomain positive weight hd
  let hsW : IncrementsOriginalSmoothInputs data := repairReferenceWeightedSmooth positive weight hs
  have transition : RepairOriginalTransitionBudgets positive Parameter Spatial :=
    ⟨hParameterTransitions,hSpatialTransitions⟩
  have hp : IncrementsOriginalPhaseConditions data hdW hsW := repair_reference_original_factory_native_phases b seed hF
    (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x) S
    O K center family hseed outer
    hSample hSEval (repairReferenceFactoryPositiveReserve b) T hT label hDistinct
    Parameter Spatial hSpatial hd hs transition
  refine ⟨label,hBound,hDistinct,?_⟩
  change ∃ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
    IncrementsOriginalPhaseConditions data hd hs ∧
    IncrementsOriginalFreeNormalConditions data hd hs ∧
    IncrementsOriginalQualitativeDecompositionInputs data ∧
    IncrementsOriginalDecompositionReserveInputs data (repairReferenceFactoryPositiveReserve b/cap^2) ∧
    IncrementsOriginalLinearSmoothInputs data ∧
    (∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport (data.cutoff nu))).card ≤ labelBound) ∧
    RepairOriginalTransitionBudgets data Parameter Spatial
  refine ⟨hdW,hsW,hp,?_,?_,?_,?_,?_,?_⟩
  · exact repair_reference_weighted_normal positive weight (fun nu => (hWeight nu).ne') hd hs hn
  · exact repair_reference_weighted_decomposition positive weight hWeight hd hs hD
  · exact repair_reference_weighted_reserve positive weight cap (repairReferenceFactoryPositiveReserve b)
      hCap hWeight hWeightCap hr
  · exact repair_reference_positive_weighted_family_linear_smooth b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x) S
      O K center family hseed outer
      (repairReferenceFactoryPositiveReserve b) weight
  · exact increment_reference_primary_multiplicity positive label labelBound hBound hDistinct weight
  · exact ⟨hParameterTransitions,hSpatialTransitions⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.closureNov_original_weighted_family_realization
