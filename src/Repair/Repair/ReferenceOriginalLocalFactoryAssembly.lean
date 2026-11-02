import Repair.ReferenceOriginalLocalFactoryPositive

/-! The all-host producer. Its inputs contain only the original map/tensor
norms, original coordinates and fixed geometric sampling data. The local
templates, finite refinements, actual normals and global native datum are
constructed by the existing Round4 theorem, rather than supplied as inputs. -/

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
private local instance assemblyFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance assemblyFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance assemblyFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

/-- Primitive original norms and explicitly specified buffered sampling
geometry. No phase, refinement, normal, step or output bound is a field. -/
structure RepairReferenceOriginalFactoryInputs
    (b : RepairReferenceFactoryBudget m d N)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ)) where
  sample_domain : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i
  map_smooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0 i)
    (incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
  map_bound : paperAtlasCj 3 (incrementsOriginalMapCoordinates seed.atlas seed.parameterChart seed.F0)
    (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal b.mapC3
  tensor_smooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart Htensor i)
    (incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
  tensor_bound : paperAtlasCj 1 (incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart Htensor)
    (incrementsOriginalDifferentiation seed.atlas seed.parameterChart) S ≤ ENNReal.ofReal b.tensorC1
  tensor_symmetric : ∀ p x, (Htensor p x).IsSymm
  outerDomain : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X
  innerCarrier : (Fin seed.atlas.count × Fin seed.parameterCount) → Set X
  center : (Fin seed.atlas.count × Fin seed.parameterCount) → X
  domain_open : ∀ i, IsOpen (outerDomain i)
  domain_convex : ∀ i, Convex ℝ (outerDomain i)
  domain_sample : ∀ i z, z ∈ outerDomain i → parameterTensorModelEquiv (m+1) d z ∈ S i
  inner_ball : ∀ i, innerCarrier i ⊆ closedBall (center i) b.modelRadius
  inner_buffer : ∀ i z, z ∈ innerCarrier i → ball z b.buffer ⊆ outerDomain i
  best_phase : ∀ i z, z ∈ innerCarrier i →
    b.phaseMargin ≤ bestPhaseSupremum (repairReferenceFactoryField seed Htensor i z).1
  tensor_lower : ∀ i z, z ∈ innerCarrier i → ∀ v : D,
    b.tensorLower*‖v‖^2 ≤ round4OriginalNativeTensorCoordinates seed.atlas seed.parameterChart Htensor i z v v
  first_lower : ∀ i z, z ∈ outerDomain i → ∀ v : D, b.firstLower*‖v‖^2 ≤
    ‖fderiv ℝ ((fun x => seed.F0 ((seed.parameterChart i.2).symm z.1,x)) ∘
      (seed.atlas.chart i.1).symm) z.2 v‖^2

def RepairReferenceOriginalFactoryInputs.family
    {b : RepairReferenceFactoryBudget m d N}
    {seed : RepairOriginalReferenceSeed (m+1) d N M P}
    {hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x))}
    {Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
    {S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ)}
    (input : RepairReferenceOriginalFactoryInputs b seed hF Htensor S)
    (hseed : RepairReferenceSeedDomains seed) (i : Fin seed.atlas.count × Fin seed.parameterCount) :
    RepairReferenceOriginalLocalFactory b seed hF Htensor S i
      (input.outerDomain i) (input.innerCarrier i) (input.center i) :=
  Classical.choice (repair_reference_original_local_factory b seed hF S input.sample_domain input.map_smooth
    input.map_bound Htensor input.tensor_smooth input.tensor_bound input.tensor_symmetric i
    (hseed.atlas_smooth.chart_mem i.1) (input.outerDomain i) (input.innerCarrier i) (input.center i)
    (input.domain_open i) (input.domain_convex i) (input.domain_sample i) (input.inner_ball i)
    (input.inner_buffer i) (input.best_phase i) (input.tensor_lower i) (input.first_lower i))

/-- Actual finite reference-data production from the primitive allowed class.
The numerical reserve and label bound are independent of both atlas counts. -/
theorem repair_reference_original_factory_realization
    (b : RepairReferenceFactoryBudget m d N) (Ds Dp : ℕ)
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
    (input : RepairReferenceOriginalFactoryInputs b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x) S)
    (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,X) 𝓘(ℝ,V) ∞ seed.F0)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (hOuterSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hOuterPartition : ∀ p ∈ seed.parameterOpen, ∀ x, ∑ i, outer i (p,x)^2=1)
    (hOuterCarrier : ∀ i, tsupport (outer i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
        ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' input.innerCarrier i)
    (sourceSupport : Fin seed.atlas.count → Set M)
    (parameterSupport : Fin seed.parameterCount → Set P)
    (hDs : ∀ i, tensorEnlargedSupportDegree sourceSupport i ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree parameterSupport i ≤ Dp)
    (hOuterSupport : ∀ i, tsupport (outer i) ⊆ parameterSupport i.2 ×ˢ sourceSupport i.1) :
    let family := input.family hseed
    let raw := repairReferenceOriginalFamilyData b seed hF
      (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x)
      S input.outerDomain input.innerCarrier input.center family hseed outer
    let data := repairReferencePositiveData raw (repairReferenceFactoryPositiveReserve b)
    ∃ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
      IncrementsOriginalFreeNormalConditions data hd hs ∧
      IncrementsOriginalQualitativeDecompositionInputs data ∧
      IncrementsOriginalDecompositionReserveInputs data (repairReferenceFactoryPositiveReserve b) ∧
      ∃ label : Fin data.primaryCount → ℕ,
        (∀ nu, label nu < ((Ds+2)*(Dp+2))*(b.pieceBound*Fintype.card Edge)) ∧
        ∀ nu mu, nu ≠ mu → (tsupport (data.cutoff nu) ∩ tsupport (data.cutoff mu)).Nonempty →
          label nu ≠ label mu := by
  intro family raw data
  obtain ⟨hd,hs,hn,hdecomp,hreserve⟩ := repair_reference_original_family_positive b seed hF S
    input.outerDomain input.innerCarrier input.center family hseed hFjoint input.sample_domain
    input.domain_sample outer hOuterSmooth hOuterPartition hOuterCarrier
  obtain ⟨label,hBound,hDistinct⟩ := repair_reference_original_family_labels b seed hF
    (fun p x => inducedMetric («I» := I) (fun y => seed.F0 (p,y)) x) S
    input.outerDomain input.innerCarrier input.center family hseed outer
    sourceSupport parameterSupport Ds Dp hDs hDp hOuterSupport
  exact ⟨hd,hs,hn,hdecomp,hreserve,label,hBound,hDistinct⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.RepairReferenceOriginalFactoryInputs.family
#print axioms GlobalEmbedding.Continuation.repair_reference_original_factory_realization
