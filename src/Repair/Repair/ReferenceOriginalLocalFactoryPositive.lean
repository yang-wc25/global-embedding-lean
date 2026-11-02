import Repair.ReferenceOriginalLocalFactoryGlobal
import Repair.EndpointTemplateDecomposition
import Repair.EndpointFactoryTensorIdentity

/-! The actual allowed-class local factories produce the original positive
reference neighborhood and the exact original tensor decomposition. The
coefficient reserve is selected from the common numerical template cover,
before the reference field and both original atlas cardinalities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
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
private local instance positiveFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance positiveFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance positiveFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

def repairReferenceFactoryPositiveReserve (b : RepairReferenceFactoryBudget m d N) : ℝ :=
  b.cover.coefficientReserve/2

theorem repair_reference_factory_positive_reserve_pos (b : RepairReferenceFactoryBudget m d N) :
    0 < repairReferenceFactoryPositiveReserve b :=
  div_pos b.cover.coefficientReserve_pos (by norm_num)

theorem repair_reference_original_family_positive
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (O K : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X)
    (center : (Fin seed.atlas.count × Fin seed.parameterCount) → X)
    (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x) S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ seed.F0)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuterSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hOuterPartition : ∀ p ∈ seed.parameterOpen, ∀ x, ∑ i, outer i (p,x)^2=1)
    (hOuterCarrier : ∀ i, tsupport (outer i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
        ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i) :
    let raw := repairReferenceOriginalFamilyData b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x)
      S O K center family hseed outer
    let data := repairReferencePositiveData raw (repairReferenceFactoryPositiveReserve b)
    ∃ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
      IncrementsOriginalFreeNormalConditions data hd hs ∧
      IncrementsOriginalQualitativeDecompositionInputs data ∧
      IncrementsOriginalDecompositionReserveInputs data (repairReferenceFactoryPositiveReserve b) := by
  intro raw data
  let Piece : (Fin seed.atlas.count × Fin seed.parameterCount) → Type := fun i => ↥(family i).s
  let Htensor := fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x
  let inner := repairReferenceOriginalFamilyInner b seed hF Htensor S O K center family
  let actual := fun a : (Σ i, Piece i × Edge) => (family a.1).actualNormal a.2.1 a.2.2
  obtain ⟨hd,hs,hn⟩ := repair_reference_original_family_admissibility b seed hF Htensor S O K center
    family hseed hFjoint hSO hSample outer hOuterSmooth
  have hInner : ∀ p ∈ seed.parameterOpen, ∀ x i, outer i (p,x) ≠ 0 →
      ∑ q, inner i q (p,x)^2 = 1 := by
    intro p hp x i hi
    have hz := hOuterCarrier i (subset_tsupport _ hi)
    have hpart := (family i).square_partition _ ((family i).cover hz.2)
    simpa only [inner, repairReferenceOriginalFamilyInner,
      repair_reference_chart_cutoff_on_source _ _ hz.1] using hpart
  have hTensor : ∀ nu z, z ∈ incrementsOriginalRelativeCutoffSupport raw nu →
      let a := repairTemplateIndex (m := m) (Piece := Piece) nu
      repairNativeTensorPullback
        (repairHostTensorInverse (seed.atlas.chart a.1.1) (hseed.atlas_smooth.chart_mem a.1.1) z.2)
        (Htensor z.1 z.2) ∈ (b.cover.template ((family a.1).pick a.2.1)).tensorDomain := by
    intro nu z hz
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    have hdomain := hd.cutoff_support_local nu hz
    change z ∈ ((seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)).source ∩
      ((seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)) ⁻¹'
        round4NormalCutoffCarrier ((family a.1).charts a.2.1 a.2.2).chart
          a.2.1.val b.normalRadius at hdomain
    have hT := ((family a.1).charts a.2.1 a.2.2).tensor_domain _ hdomain.2.1
    change round4OriginalNativeTensorCoordinates seed.atlas seed.parameterChart Htensor a.1
      (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2) ∈ _ at hT
    rw [repair_factory_tensor_at_original_point seed.atlas seed.parameterChart Htensor a.1
      (hseed.atlas_smooth.chart_mem a.1.1) z.1 hdomain.1.1 z.2 hdomain.1.2] at hT
    exact hT
  have hdecomp := repair_original_template_positive_decomposition
    (Host := Fin seed.atlas.count × Fin seed.parameterCount) (Piece := Piece)
    seed (fun i => seed.atlas.chart i.1) (fun i => hseed.atlas_smooth.chart_mem i.1)
    (fun i q => b.cover.template ((family i).pick q)) outer inner
    (fun a => repairReferenceActualNormalField seed hF (seed.parameterChart a.1.2)
      (seed.atlas.chart a.1.1) ((b.cover.template ((family a.1).pick a.2.1)).covectors a.2.2) (actual a))
    (fun a => repairReferenceActualNormalDomain seed hF (seed.parameterChart a.1.2)
      (seed.atlas.chart a.1.1) ((b.cover.template ((family a.1).pick a.2.1)).covectors a.2.2) (actual a))
    (repairReferenceFactoryPositiveReserve b) (repair_reference_factory_positive_reserve_pos b)
    (fun i q => (half_lt_self b.cover.coefficientReserve_pos).trans_le
      (b.cover.bounds ((family i).pick q)).2.1)
    hOuterPartition hInner
    (fun p _ x i hi => (hOuterCarrier i (subset_tsupport _ hi)).1.2) hTensor
  obtain ⟨hd',hs',hn'⟩ := repair_reference_positive_admissibility raw
    (repairReferenceFactoryPositiveReserve b) hd hs hn
  exact ⟨hd',hs',hn',hdecomp.1,hdecomp.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_positive
