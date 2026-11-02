import Repair.EntranceOriginalFactoryKernel
import Repair.EntranceSpatialPrimaryFactory
import Repair.EntranceSpatialPrimaryObserver
import Repair.ReferenceOriginalLocalFactoryPrimarySupply
import Repair.ReferenceOriginalLocalFactoryDomains
import Repair.ReferenceOriginalLocalFactoryPlateauJets
import Repair.IncrementRegionTransitionBudget
import Repair.IncrementGivenPhaseTransitions

/-!
# The whole primary budget is manufactured from the actual original factory

No primary packet, reference profile, observer budget, adapted cutoff jet,
or primary kernel bound is an input. All are produced from the original
template factory, actual parent cutoffs, original norm-domain sampling and
the original transition budget. Every returned numerical profile is fixed
by the displayed numerical inputs before the reference map is selected.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation

def repairEntranceFactoryNativeForward {m d N : ℕ}
    (b : RepairReferenceFactoryBudget m d N) (cap Bp Bs : ℝ) (Spatial : ℕ → ℝ) :=
  repairEntranceSpatialNativeForward (max Bp Bs) (2*(1+2*(cap*b.cover.covectorBound))) Spatial

def repairEntranceFactoryNativeInverse {m d N : ℕ}
    (b : RepairReferenceFactoryBudget m d N) (cap Bp Bs : ℝ) (Spatial : ℕ → ℝ) :=
  repairEntranceSpatialNativeInverse (max Bp Bs)
    (2*actualPhaseInverseConstant b.covectorLower (2*(cap*b.cover.covectorBound))) Spatial

def repairEntranceFactoryForward {m d N : ℕ}
    (b : RepairReferenceFactoryBudget m d N) (cap Bp Bs : ℝ) (Parameter Spatial : ℕ → ℝ) :=
  repairEntranceOriginalForwardProfile Bp (repairEntranceFactoryNativeForward b cap Bp Bs Spatial)
    Parameter Spatial

def repairEntranceFactoryInverse {m d N : ℕ}
    (b : RepairReferenceFactoryBudget m d N) (cap Bp Bs : ℝ) (Parameter Spatial : ℕ → ℝ) :=
  repairEntranceOriginalInverseProfile Bp Bs (repairEntranceFactoryNativeInverse b cap Bp Bs Spatial)
    Parameter Spatial

def repairEntranceFactoryCutoff {m d N : ℕ}
    (b : RepairReferenceFactoryBudget m d N) (Parent Parameter Spatial : ℕ → ℝ) :=
  tensorProductJetConstant Parent
    (repairEntranceCompositionProfile (repairReferenceFactoryPlateauProfile b)
      (fun j => max (Parameter j) (Spatial j)))

def repairEntranceFactoryMeta {m d N : ℕ}
    (b : RepairReferenceFactoryBudget m d N) (cap Bp Bs : ℝ) (Parent Parameter Spatial : ℕ → ℝ) :=
  repairEntranceCompositionProfile (repairEntranceFactoryCutoff b Parent Parameter Spatial)
    (repairEntranceFactoryInverse b cap Bp Bs Parameter Spatial)

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

theorem repairEntrance_actual_original_primary_factory
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
    (hInner : ∀ i z, z ∈ O i → (seed.atlas.chart i.1).symm z.2 ∈ seed.atlas.inner i.1)
    (outer theta : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hThetaCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hThetaSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      (seed.parameterChart i.2).source ×ˢ (seed.atlas.chart i.1).source)
    (hThetaK : ∀ i z, z ∈ tsupport (theta i) →
      (seed.parameterChart i.2 z.1,seed.atlas.chart i.1 z.2) ∈ K i)
    (rho cap T Bp Bs lower C2 : ℝ)
    (hCap : 1 ≤ cap) (hT : 0 < T) (hBp : 0 ≤ Bp) (hBs : 0 ≤ Bs)
    (hLower : 0 < lower) (hC2 : 0 ≤ C2)
    (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (hWeight : ∀ nu, 1 ≤ weight nu) (hWeightCap : ∀ nu, weight nu ≤ cap)
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
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    let NF := repairEntranceFactoryNativeForward b cap Bp Bs Spatial
    let NI := repairEntranceFactoryNativeInverse b cap Bp Bs Spatial
    let FC := repairEntranceFactoryForward b cap Bp Bs Parameter Spatial
    let IC := repairEntranceFactoryInverse b cap Bp Bs Parameter Spatial
    let MC := repairEntranceFactoryMeta b cap Bp Bs Parent Parameter Spatial
    let kappa := b.cover.restrictionReserve/T^2
    ∀ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
      (hn : IncrementsOriginalFreeNormalConditions data hd hs)
      (hAll : data.parameterSet=univ)
      (hJoint : ContMDiff IJ 𝓘(ℝ,Ey) ∞ data.F)
      (transition : RepairOriginalTransitionBudgets data Parameter Spatial)
      (hEll : IncrementsOriginalCoordinateEllipticityInputs data lower)
      (hCompact : ∀ i, IsCompact (incrementsOriginalEvaluation data.atlas data.parameterChart
        data.sourceNormDomain data.parameterNormDomain data.parameterSet i))
      (hMap : (paperAtlasCj 2 (incrementsOriginalMapCoordinates data.atlas data.parameterChart data.F)
        (incrementsOriginalDifferentiation data.atlas data.parameterChart)
        (incrementsOriginalEvaluation data.atlas data.parameterChart data.sourceNormDomain
          data.parameterNormDomain data.parameterSet)).toReal ≤ C2),
    ∃ (packet : Round3ParameterWholePrimaryPieceSupply data theta)
      (profiles : Round3ParameterWholeReferenceProfiles data hd hs theta packet)
      (observer : RepairPrimaryObserverBudget data hd hs theta packet profiles),
      profiles.piece=packet.piece ∧
      profiles.cF=lower/(1+NF 1)^2 ∧
      profiles.cT=(kappa/((1+NF 1)^2*actualIncrementSortedSymmetricConstant m))^2 ∧
      profiles.MH=actualFirstFrameTransferCost NI 1*(actualOriginalMapJetCost (m+1) d N 0*C2) ∧
      profiles.Tinv=NI ∧ profiles.Tforward=NF ∧
      observer.forwardProfile=FC ∧ observer.inverseProfile=IC ∧
      (∀ j, 0 ≤ MC j) ∧
      (∀ nu i a y, y ∈ tsupport (packet.piece nu i a).cutoff → y.1 ∈ data.parameterNormDomain i.2) ∧
      RepairOriginalPrimaryCutoffJets data
        (round3ParameterWholePrimaryFamily data hd hs hn theta
          (round3OuterReferencePrimaryPacket data hd hs theta packet profiles)) MC := by
  intro raw data NF NI FC IC MC kappa hd hs hn hAll hJoint transition hEll hCompact hMap
  let index := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s)
  let owner := repairReferenceOriginalFamilyOwner b seed hF Htensor S O K center family
  have hOwn (nu : Fin data.primaryCount) (z : P × M) (hz : z ∈ data.primaryDomain nu) :=
    repair_reference_original_family_owner_samples b seed hF Htensor S O K center family
      hseed outer hSample hSEval nu z hz
  have hSamples (i : Fin data.atlas.count × Fin data.parameterCount) (z : X) (hz : z ∈ O i) :
      parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation data.atlas data.parameterChart
        data.sourceNormDomain data.parameterNormDomain data.parameterSet i := hSEval i (hSample i z hz)
  have hUOpen (i : Fin data.atlas.count × Fin data.parameterCount) : O i ⊆ actualOriginalNativeOpen data i :=
    fun z hz => actualOriginalNativeOpen_evaluation_subset data hd i (hSamples i z hz)
  have hUCover (i : Fin data.atlas.count × Fin data.parameterCount) (z : P × M)
      (hz : z ∈ tsupport (theta i)) :
      (data.parameterChart i.2 z.1,data.atlas.chart i.1 z.2) ∈ O i :=
    (family i).partition_domain ((family i).cover (hThetaK i z hz))
  have hFirst (nu : Fin data.primaryCount) (i : Fin data.atlas.count × Fin data.parameterCount)
      (z : X) (hz : z ∈ O i)
      (ht : z ∈ (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)).source)
      (_ : ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm z.2) ∈ data.primaryDomain nu) :
      ‖fderiv ℝ (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)) z‖ ≤ T := by
    have he := (actual_original_native_evaluation_iff data hd i z).mp (hSamples i z hz)
    have h := transition.spatial i.1 (index nu).1.1 1 le_rfl z he.1 ht
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans hTbound
  obtain ⟨s⟩ := repair_reference_original_factory_primary_supply b seed hF Htensor S O K center family
    hseed hSO hSample outer theta hThetaCompact hThetaSmooth hThetaSource rho cap T hCap hT
    weight hWeight hWeightCap O hO hUCover
    (fun nu i z hz ha ht => hFirst nu i z hz ht ha) hd hUOpen
  have hMu := (round4UniformTemplateCovectorLower_spec D Ey b.templateDim b.operatorBound
    b.phaseMargin b.tensorLower b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos).1
  have hBound : 0 ≤ cap*b.cover.covectorBound := mul_nonneg (zero_le_one.trans hCap) b.cover.covectorBound_pos.le
  have hV : 0 ≤ max Bp Bs := hBp.trans (le_max_left _ _)
  have hSourceValues (i) (z : X) (hz : z ∈ O i) : ‖z‖ ≤ max Bp Bs := by
    have h := (actual_original_native_evaluation_iff data hd i z).mp (hSamples i z hz)
    exact max_le_max (hParameterValue i.2 z.1 h.2.1) (hSourceValue i.1 z.2 h.1)
  have hOwnerSource (nu : Fin data.primaryCount) (z : P × M) (hz : z ∈ data.primaryDomain nu) :
      z.2 ∈ (owner nu).source := (hOwn nu z hz).1
  have hOwnerValues (nu) (i) (z : X) (hz : z ∈ O i)
      (_ : z ∈ (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)).source)
      (hActive : ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm z.2) ∈ data.primaryDomain nu) :
      ‖repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu) z‖ ≤ max Bp Bs := by
    have h := (actual_original_native_evaluation_iff data hd i z).mp (hSamples i z hz)
    exact max_le_max (hParameterValue i.2 z.1 h.2.1)
      (hSourceValue (index nu).1.1 _ (hOwn nu _ hActive).2.1)
  have hForwardJets (nu) (i) (j : ℕ) (hj : 1 ≤ j) (z : X) (hz : z ∈ O i)
      (ht : z ∈ (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)).source)
      (_ : ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm z.2) ∈ data.primaryDomain nu) :
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)) z‖ ≤ Spatial j := by
    exact transition.spatial i.1 (index nu).1.1 j hj z
      ((actual_original_native_evaluation_iff data hd i z).mp (hSamples i z hz)).1 ht
  have hInverseJets (nu) (i) (j : ℕ) (hj : 1 ≤ j) (z : X)
      (ht : z ∈ (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)).target)
      (_ : (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)).symm z ∈ O i)
      (hActive : ((data.parameterChart i.2).symm z.1,(owner nu).symm z.2) ∈ data.primaryDomain nu) :
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (data.atlas.chart i.1) (owner nu)).symm z‖ ≤ Spatial j := by
    have hSampleOwn := (hOwn nu _ hActive).2.1
    change owner nu ((owner nu).symm z.2) ∈ seed.sourceNormDomain (index nu).1.1 at hSampleOwn
    rw [(owner nu).right_inv ht.2.1] at hSampleOwn
    exact transition.spatial (index nu).1.1 i.1 j hj z hSampleOwn ht
  have hReverse (nu) (i) (z : X) (hz : z ∈ O i)
      (hActive : ((data.parameterChart i.2).symm z.1,(data.atlas.chart i.1).symm z.2) ∈ data.primaryDomain nu) :
      ‖fderiv ℝ (seed.atlas.chart i.1 ∘ (seed.atlas.chart (index nu).1.1).symm)
        (seed.atlas.chart (index nu).1.1 ((seed.atlas.chart i.1).symm z.2))‖ ≤ T := by
    have hOwn' := hOwn nu _ hActive
    have hOpen := (round3Parameter_originalNativeOpen_iff data i z).mp (hUOpen i hz)
    apply (increment_actual_spatial_transition_first data hd Parameter Spatial transition
      (index nu).1.1 i.1 _ ((owner nu).map_source hOwn'.1) _ hOwn'.2.1).trans hTbound
    change (owner nu).symm (owner nu ((data.atlas.chart i.1).symm z.2)) ∈ (data.atlas.chart i.1).source
    rw [(owner nu).left_inv hOwn'.1]
    exact (data.atlas.chart i.1).map_target hOpen.1
  have hKernel := repairEntrance_original_factory_kernel_inputs b seed hF Htensor S O K center family
    hseed outer rho weight (fun nu => (zero_lt_one.trans_le (hWeight nu)).ne') T hT O hUOpen hReverse
  have hkappa : 0 < kappa := div_pos b.cover.restrictionReserve_pos (sq_pos_of_pos hT)
  obtain ⟨profiles,hPiece,hCF,hCT,hMH,hNI,hNF⟩ := s.numerical_reference_profiles
    hMu hBound hUOpen hOwnerSource (max Bp Bs) hV Spatial hSpatial hSourceValues hOwnerValues
    hForwardJets hInverseJets hSamples hInner kappa hKernel hd hs hAll hJoint
    lower C2 hkappa hLower hC2 hEll hCompact hMap
  let observer := s.observer_budget hd hs profiles hPiece Parameter Spatial hParameter hSpatial transition
    Bp Bs hBp hBs hParameterValue hSourceValue hSamples
  have hFC : observer.forwardProfile=FC := by
    dsimp only [observer,RepairReferenceSpatialPrimarySupply.observer_budget,
      RepairPrimaryObserverBudget.forwardProfile,FC,repairEntranceFactoryForward]
    rw [hNF]
    rfl
  have hIC : observer.inverseProfile=IC := by
    dsimp only [observer,RepairReferenceSpatialPrimarySupply.observer_budget,
      RepairPrimaryObserverBudget.inverseProfile,IC,repairEntranceFactoryInverse]
    rw [hNI]
    rfl
  let Joint := fun j => max (Parameter j) (Spatial j)
  have hJointProfile : ∀ j, 0 ≤ Joint j := fun j => (hParameter j).trans (le_max_left _ _)
  let Cutoff := repairEntranceFactoryCutoff b Parent Parameter Spatial
  have hCutoff : ∀ j, 0 ≤ Cutoff j := tensorProductJetConstant_nonneg hParent
    (repairEntranceCompositionProfile_nonneg _ _ (repairReferenceFactoryPlateauProfile_nonneg b) hJointProfile)
  have hMC : ∀ j, 0 ≤ MC j := by
    rw [show MC=repairEntranceCompositionProfile Cutoff observer.inverseProfile by rw [hIC]; rfl]
    exact repairEntranceCompositionProfile_nonneg _ _ hCutoff observer.inverse_nonneg
  have hCut := s.numerical_meta hd hs hn profiles observer hCompact Cutoff hCutoff (by
    intro nu parent i j z hz
    have hNative := (actual_original_native_evaluation_iff data hd i z).mp hz
    have hzTarget : z ∈ ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).target :=
      ⟨hd.parameter_norm_subset i.2 hNative.2.1,hd.source_norm_subset i.1 hNative.1⟩
    apply repair_reference_original_family_primary_cutoff_observer_jets b seed hF Htensor S O K center family
      hseed hSO hSample (theta parent) (hThetaSmooth parent) Parent Joint hParent hJointProfile
      nu i z hzTarget (fun k => hParentJets parent i k z hz) _ j
    intro k hk
    dsimp only
    intro hOwner
    have h := increment_given_actual_native_transition_jets data hd Parameter Spatial transition
      (i,(index nu).1) (parameterTensorModelEquiv (m+1) d z)
      ⟨hz,⟨hz.1,by
        change incrementsOriginalJointPoint data.atlas data.parameterChart i
          (parameterTensorModelEquiv (m+1) d z) ∈
          (data.parameterChart (index nu).1.2).source ×ˢ (data.atlas.chart (index nu).1.1).source
        rw [actual_original_jointPoint_native]
        exact hOwner⟩⟩ k hk
    change ‖iteratedFDeriv ℝ k (fun w : X =>
      (data.parameterChart (index nu).1.2 ((data.parameterChart i.2).symm w.1),
        data.atlas.chart (index nu).1.1 ((data.atlas.chart i.1).symm w.2))) z‖ ≤
      max (Parameter k) (Spatial k)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h.2)
  have hPrimaryParam : ∀ nu i a y, y ∈ tsupport (s.packet.piece nu i a).cutoff →
      y.1 ∈ data.parameterNormDomain i.2 := by
    intro nu i a y hy
    have hNative := round3Parameter_native_compact_parent (data.parameterChart i.2)
      (hd.parameter_charts_smooth i.2) (theta i) (hThetaCompact i) (hThetaSmooth i)
      (fun z hz => ⟨(hThetaSource i hz).1,mem_univ _⟩)
    obtain ⟨z,hz,rfl⟩ := hNative.2.2 (s.packet.native_parent nu i a hy)
    have hU := hUCover i z hz
    exact ((actual_original_native_evaluation_iff data hd i _).mp (hSamples i _ hU)).2.1
  refine ⟨s.packet,profiles,observer,hPiece,hCF,hCT,hMH,hNI,hNF,hFC,hIC,hMC,hPrimaryParam,?_⟩
  simpa only [MC,repairEntranceFactoryMeta,Cutoff,hIC] using hCut

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_original_primary_factory
