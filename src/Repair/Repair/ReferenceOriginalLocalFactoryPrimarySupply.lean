import Repair.ReferenceOriginalLocalFactoryPlateau
import Repair.ReferenceOriginalLocalFactoryPhases
import Repair.ReferenceSpatialPrimarySupply

/-! The actual bounded local factories, their genuine zero-extended plateaus,
and the common phase hierarchy produce the entire primary piece packet.
The source and parameter observing charts are the original charts, and
all physical domains and the same original cutoffs are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle Filter
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
private local instance plateauFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance plateauFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance plateauFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
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


include hF Htensor O K center in
def repairReferenceOriginalFamilyOwner
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) : OpenPartialHomeomorph M D :=
  seed.atlas.chart (repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu).1.1

include hF Htensor O K center in
def repairReferenceOriginalFamilyWeightedCovector
    (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) : D →L[ℝ] ℝ :=
  let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  weight nu • (b.cover.template ((family a.1).pick a.2.1)).covectors a.2.2

include hF Htensor O K center in
theorem repair_reference_original_factory_primary_supply
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer theta : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      (seed.parameterChart i.2).source ×ˢ (seed.atlas.chart i.1).source)
    (rho cap T : ℝ) (hCap : 1 ≤ cap) (hT : 0 < T)
    (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ)
    (hWeight : ∀ nu, 1 ≤ weight nu) (hWeightCap : ∀ nu, weight nu ≤ cap)
    (U : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (hU : ∀ i, IsOpen (U i))
    (hUCover : ∀ i z, z ∈ tsupport (theta i) →
      (seed.parameterChart i.2 z.1,seed.atlas.chart i.1 z.2) ∈ U i)
    (hTransition : ∀ nu i z, z ∈ U i →
      ((seed.parameterChart i.2).symm z.1,(seed.atlas.chart i.1).symm z.2) ∈
        (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryDomain nu →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (seed.atlas.chart i.1)
        (repairReferenceOriginalFamilyOwner b seed hF Htensor S O K center family nu)).source →
      ‖fderiv ℝ (repairReferenceHostTransition («Ep» := Ep) (seed.atlas.chart i.1)
        (repairReferenceOriginalFamilyOwner b seed hF Htensor S O K center family nu)) z‖ ≤ T) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data)
      (hUOpen : ∀ i, U i ⊆ actualOriginalNativeOpen data i),
      Nonempty (RepairReferenceSpatialPrimarySupply data theta
        (repairReferenceOriginalFamilyOwner b seed hF Htensor S O K center family)
        (repairReferenceOriginalFamilyWeightedCovector b seed hF Htensor S O K center family weight)
        (repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family)
        U b.covectorLower (cap*b.cover.covectorBound)) := by
  intro raw data hd hUOpen
  let index := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s)
  have hEta := round4UniformTemplateCovectorLower_spec D V b.templateDim b.operatorBound
    b.phaseMargin b.tensorLower b.nativeTensor1 b.phaseMargin_pos b.tensorLower_pos
  have hProperties := repair_reference_original_family_plateau_properties
    b seed hF Htensor S O K center family hseed hSO hSample outer
  apply repair_reference_actual_spatial_primary_supply b.covectorLower (cap*b.cover.covectorBound)
    T hEta.1 (mul_nonneg (zero_le_one.trans hCap) b.cover.covectorBound_pos.le) hT
    data hd theta hCompact hSmooth hThetaSource
    (repairReferenceOriginalFamilyOwner b seed hF Htensor S O K center family)
    (fun nu => hseed.atlas_smooth.chart_mem (index nu).1.1)
    (repairReferenceOriginalFamilyWeightedCovector b seed hF Htensor S O K center family weight)
    _ _ _ _
    (repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family)
    (fun nu => (hProperties nu).2.1) (fun nu => (hProperties nu).2.2.1)
    (fun nu => (hProperties nu).2.2.2) U hU hUOpen hUCover hTransition
  · intro nu
    change b.covectorLower ≤ ‖weight nu • (b.cover.template ((family (index nu).1).pick (index nu).2.1)).covectors (index nu).2.2‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans_le (hWeight nu))]
    have hw := hWeight nu
    have hl := hEta.2 ((family (index nu).1).pick (index nu).2.1) (index nu).2.2
    change b.covectorLower ≤ ‖(b.cover.template ((family (index nu).1).pick (index nu).2.1)).covectors (index nu).2.2‖ at hl
    exact hl.trans (by nlinarith [norm_nonneg ((b.cover.template ((family (index nu).1).pick (index nu).2.1)).covectors (index nu).2.2)])
  · intro nu
    change ‖weight nu • (b.cover.template ((family (index nu).1).pick (index nu).2.1)).covectors (index nu).2.2‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans_le (hWeight nu))]
    exact mul_le_mul (hWeightCap nu) ((b.cover.bounds _).2.2.2.2 _) (norm_nonneg _) (zero_le_one.trans hCap)
  · intro nu z
    rfl
  · intro nu z hz
    exact (repair_reference_original_family_operator b seed hF Htensor S O K center family
      hseed outer nu z hz).1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_factory_primary_supply
