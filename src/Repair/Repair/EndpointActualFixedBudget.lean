import Repair.EndpointFactoryObservedJets
import Repair.EndpointFixedReferenceProfile
import Repair.EndpointFixedPacketAssembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance globalFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance globalFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

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
private local instance globalFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance globalFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance globalFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

variable (b : RepairReferenceFactoryBudget m d N)
  (seed : RepairOriginalReferenceSeed (m+1) d N M P)
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F0 (p,x)))
  (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
  (O K : (Fin seed.atlas.count × Fin seed.parameterCount) →
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))))
  (center : (Fin seed.atlas.count × Fin seed.parameterCount) →
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
  (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))


private theorem repair_six_cost_bounds (a b c d e f K : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) (hK : 0 ≤ K) :
    K*a ≤ K*(a+b+c+d+e+f) ∧ K*b ≤ K*(a+b+c+d+e+f) ∧ K*c ≤ K*(a+b+c+d+e+f) ∧
    K*d ≤ K*(a+b+c+d+e+f) ∧ K*e ≤ K*(a+b+c+d+e+f) ∧ K*f ≤ K*(a+b+c+d+e+f) := by
  exact ⟨mul_le_mul_of_nonneg_left (by linarith) hK,
    mul_le_mul_of_nonneg_left (by linarith) hK,
    mul_le_mul_of_nonneg_left (by linarith) hK,
    mul_le_mul_of_nonneg_left (by linarith) hK,
    mul_le_mul_of_nonneg_left (by linarith) hK,
    mul_le_mul_of_nonneg_left (by linarith) hK⟩

include hF Htensor O K center in
/-- The full original fixed-packet bound is produced for the same actual
weighted local factory datum. No normal, cutoff, phase, coefficient or
transition-output norm is assumed. The numerical profile precedes both
atlas counts and reads the original reference map only through j+2. -/
theorem repair_reference_actual_factory_fixed_budget
    (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ seed.F0)
    (hOpen : seed.parameterOpen=univ)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hSupport : ∀ i, tsupport (outer i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source)
    (R Parent Parameter Spatial : ℕ → ℝ)
    (hR : ∀ j, 0 ≤ R j) (hParent : ∀ j, 0 ≤ Parent j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (hMap : ∀ j, paperAtlasCj (j+2)
      (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
      (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal (R (j+2)))
    (Bs : ℝ) (hBs : 0 ≤ Bs)
    (hRadius : ∀ i x, x ∈ seed.sourceNormDomain i → ‖x‖ ≤ Bs)
    (hParentJets : ∀ owner i k y, y ∈ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i →
      ‖iteratedFDeriv ℝ k (outer owner ∘ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).symm)
        ((parameterTensorModelEquiv (m+1) d).symm y)‖ ≤ Parent k)
    (rho transitionBound : ℝ) (hT : 0 ≤ transitionBound) (labelBound : ℕ)
    (label : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℕ)
    (hLabel : ∀ nu, label nu ≤ labelBound) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let positive := repairReferencePositiveData raw rho
    let base := repairReferenceSignedHierarchy b.cover b.operatorBound transitionBound
    let weight := fun nu => base^label nu
    let cap := base^labelBound
    let data := repairReferenceWeightedData positive weight
    RepairOriginalTransitionBudgets raw Parameter Spatial →
    ∀ j, parameterRound2_originalFixedPacketProfile data j 1 ≠ ⊤ ∧
      (parameterRound2_originalFixedPacketProfile data j 1).toReal ≤
        repairReferenceOriginalFixedProfile b cap Bs R Parent Parameter Spatial j := by
  intro raw positive base weight cap data transition j
  obtain ⟨hdRaw,hsRaw,hnRaw⟩ := repair_reference_original_family_admissibility b seed hF Htensor S O K center
    family hseed hFjoint hSO hSample outer hOuter
  obtain ⟨hdPositive,hsPositive,hnPositive⟩ := repair_reference_positive_admissibility raw rho hdRaw hsRaw hnRaw
  let hd := repairReferenceWeightedDomain positive weight hdPositive
  let hs := repairReferenceWeightedSmooth positive weight hsPositive
  have hlRaw := repair_reference_original_family_linear_smooth b seed hF Htensor S O K center family hseed outer
  have hlPositive : IncrementsOriginalLinearSmoothInputs positive := ⟨hlRaw.linear_coordinates⟩
  have hl : IncrementsOriginalLinearSmoothInputs data := repair_reference_weighted_linear_smooth positive weight hlPositive
  have hBase : 1 < base := repairReferenceSignedHierarchy_gt_one b.cover b.operatorBound transitionBound hT
  have hWeight (nu) : 1 ≤ weight nu := one_le_pow₀ hBase.le
  have hCap : 0 ≤ cap := pow_nonneg (zero_lt_one.trans hBase).le _
  let Joint := fun k => max (Parameter k) (Spatial k)
  let Cutoff := repairReferenceCutoffOriginalProfile b Parent Joint
  let Normal := repairReferenceNormalOriginalProfile b R Joint
  let Linear := repairOriginalJointLinearProfile (m+1) d b.cover.coefficientBound
    (repairOriginalSpatialFullProfile Bs Spatial)
  have hJoint : ∀ k, 0 ≤ Joint k := fun k => (hParameter k).trans (le_max_left _ _)
  have hC : ∀ k, 0 ≤ Cutoff k := repairReferenceCutoffOriginalProfile_nonneg b Parent Joint hParent hJoint
  have hN : ∀ k, 0 ≤ Normal k := repairReferenceNormalOriginalProfile_nonneg b R Joint hJoint
  have hL : ∀ k, 0 ≤ Linear k := repairOriginalJointLinearProfile_nonneg (m+1) d
    b.cover.coefficientBound b.cover.coefficientBound_pos.le _
  have hRawJets := repair_reference_original_factory_observed_jets b seed hF Htensor S O K center family
    hseed hSO hSample hSEval outer hOuter hSupport R Parent Parameter Spatial hR hParent hParameter hSpatial
    hMap Bs hBs hRadius hParentJets hdRaw transition
  have hThree (nu : Fin data.primaryCount) := repair_original_cutoff_normal_linear_norms data hd hs hl hOpen
    Cutoff Normal Linear hC hN hL
    (fun nu i k y hy => (hRawJets nu i k y hy).1)
    (fun nu i k y hy => (hRawJets nu i k y hy).2.1)
    (fun nu i k y hy => (repair_weighted_original_linear_jet_le positive hdPositive hlPositive hOpen
      weight hWeight nu i y ⟨hy.1.1,hy.2⟩ k).trans (hRawJets nu i k y hy).2.2) nu j
  have transitionData : RepairOriginalTransitionBudgets data Parameter Spatial :=
    ⟨transition.parameter,transition.spatial⟩
  have hPhases := increment_given_actual_factory_phase_norms b seed hF Htensor S O K center family hseed outer
    rho transitionBound hT labelBound label hLabel hd hs Parameter Spatial hParameter hSpatial transitionData
    j 1 zero_lt_one le_rfl
  let Ptotal := incrementGivenPhaseTotalProfile (m+1) d cap b.cover.covectorBound Spatial
  let Pspatial := incrementGivenPhaseSpatialProfile (m+1) d cap b.cover.covectorBound Spatial
  let Ptrans := incrementGivenTransitionProfile (m+1) d Parameter Spatial
  have hPT : ∀ k, 0 ≤ Ptotal k := incrementGivenPhaseTotalProfile_nonneg (m+1) d cap b.cover.covectorBound
    Spatial hCap b.cover.covectorBound_pos.le hSpatial
  have hPS : ∀ k, 0 ≤ Pspatial k := incrementGivenPhaseSpatialProfile_nonneg (m+1) d cap b.cover.covectorBound
    Spatial hCap b.cover.covectorBound_pos.le hSpatial
  have hTR : ∀ k, 0 ≤ Ptrans k := incrementGivenTransitionProfile_nonneg (m+1) d Parameter Spatial hParameter hSpatial
  have hCosts := repair_six_cost_bounds
    (repairOriginalJetPrefix Cutoff j) (repairOriginalJetPrefix Normal j) (repairOriginalJetPrefix Linear j)
    (bufferedTransitionPrefix Ptotal j) (bufferedTransitionPrefix Pspatial j) (bufferedTransitionPrefix Ptrans j)
    (j+1) (repairOriginalJetPrefix_nonneg Cutoff hC j) (repairOriginalJetPrefix_nonneg Normal hN j)
    (repairOriginalJetPrefix_nonneg Linear hL j) (zero_le_one.trans (one_le_bufferedTransitionPrefix hPT j))
    (zero_le_one.trans (one_le_bufferedTransitionPrefix hPS j)) (zero_le_one.trans (one_le_bufferedTransitionPrefix hTR j))
    (by positivity)
  apply repair_original_fixed_packet_components data j (repairReferenceOriginalFixedProfile b cap Bs R Parent Parameter Spatial j)
    (repairReferenceOriginalFixedProfile_nonneg b cap Bs hCap hBs R Parent Parameter Spatial hParent hParameter hSpatial j)
  · intro nu
    exact repair_ennreal_le_of_actual_bound (hThree nu).1.1 ((hThree nu).1.2.trans hCosts.1)
  · intro nu
    exact repair_ennreal_le_of_actual_bound (hThree nu).2.1.1 ((hThree nu).2.1.2.trans hCosts.2.1)
  · intro nu
    exact repair_ennreal_le_of_actual_bound (hPhases.1 nu).2.1 ((hPhases.1 nu).2.2.trans hCosts.2.2.2.2.1)
  · intro nu
    exact repair_ennreal_le_of_actual_bound (hThree nu).2.2.1 ((hThree nu).2.2.2.trans hCosts.2.2.1)
  · intro nu
    exact repair_ennreal_le_of_actual_bound (hPhases.1 nu).1.1 ((hPhases.1 nu).1.2.trans hCosts.2.2.2.1)
  · exact repair_ennreal_le_of_actual_bound hPhases.2.1 (hPhases.2.2.trans hCosts.2.2.2.2.2)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_factory_fixed_budget
