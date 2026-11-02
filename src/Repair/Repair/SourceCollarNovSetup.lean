import Repair.SourceCollarNovParentSquare
import Repair.SourceCollarNovParentProduct
import Repair.SourceCollarNovOriginalFactory
import Repair.EndpointTemplateData
import Repair.ReferenceTemplateAdmissibility
import Repair.EndpointSourceCompactness
import Repair.ReferenceRehostedChart
import Smoothing.ParameterRound2PreparedGeometry

/-!
# Original fixed Setup with actual auxiliary parent preparations

Only the original buffered atlases, original raw preparations and their
numerical budgets, original compact norm domains, coordinate bounds, and
positive-order original transition bounds are inputs.  No collar, normal,
adapted chart, reference map, or repair output is a field.  The auxiliary raw
preparations below are the proved fixed scalar functions of these inputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

structure SourceCollarNovSetup (n d : ℕ) (M P : Type*)
    [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] where
  source : BufferedAtlas M (EuclideanSpace ℝ (Fin n))
  parameter : BufferedAtlas P (EuclideanSpace ℝ (Fin d))
  source_smooth : IsSmoothBufferedAtlas source
  parameter_smooth : IsSmoothBufferedAtlas parameter
  BS : ℕ → ℝ
  TS : ℕ → ℝ
  BP : ℕ → ℝ
  TP : ℕ → ℝ
  BS_nonneg : ∀ j, 0 ≤ BS j
  TS_nonneg : ∀ j, 0 ≤ TS j
  BP_nonneg : ∀ j, 0 ≤ BP j
  TP_nonneg : ∀ j, 0 ≤ TP j
  Ds : ℕ
  Dp : ℕ
  sourcePreparation : TensorRawCutoffPreparation source BS TS Ds
  parameterPreparation : TensorRawCutoffPreparation parameter BP TP Dp
  Omega : Fin source.count → Set (EuclideanSpace ℝ (Fin n))
  Q : Fin parameter.count → Set (EuclideanSpace ℝ (Fin d))
  source_compact : ∀ i, IsCompact (Omega i)
  parameter_compact : ∀ i, IsCompact (Q i)
  source_target : ∀ i, Omega i ⊆ (source.chart i).target
  parameter_target : ∀ i, Q i ⊆ (parameter.chart i).target
  source_sampling : ∀ i, bufferedSamplingCoordinates source i ⊆ Omega i
  parameter_sampling : ∀ i, bufferedSamplingCoordinates parameter i ⊆ Q i
  coordinateRadius : ℝ
  coordinateRadius_nonneg : 0 ≤ coordinateRadius
  source_bound : ∀ i x, x ∈ Omega i → ‖x‖ ≤ coordinateRadius
  parameter_bound : ∀ i p, p ∈ Q i → ‖p‖ ≤ coordinateRadius
  parameterTransition : ℕ → ℝ
  spatialTransition : ℕ → ℝ
  parameterTransition_nonneg : ∀ j, 0 ≤ parameterTransition j
  spatialTransition_nonneg : ∀ j, 0 ≤ spatialTransition j
  parameter_transition_jets : ∀ (ip jp : Fin parameter.count) (k : ℕ), 1 ≤ k →
    ∀ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n), z.1 ∈ Q ip →
    z ∈ (((parameter.chart ip).symm.trans (parameter.chart jp)).prod
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))).source →
    ‖iteratedFDeriv ℝ k (((parameter.chart ip).symm.trans (parameter.chart jp)).prod
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))) z‖ ≤ parameterTransition k
  spatial_transition_jets : ∀ (i j : Fin source.count) (k : ℕ), 1 ≤ k →
    ∀ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n), z.2 ∈ Omega i →
    z ∈ ((OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin d))).prod
      ((source.chart i).symm.trans (source.chart j))).source →
    ‖iteratedFDeriv ℝ k ((OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin d))).prod
      ((source.chart i).symm.trans (source.chart j))) z‖ ≤
      spatialTransition k

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

namespace SourceCollarNovSetup
variable (g : SourceCollarNovSetup n d M P)

def seed (F0 : P × M → EuclideanSpace ℝ (Fin N)) : RepairOriginalReferenceSeed n d N M P where
  atlas := g.source
  parameterCount := g.parameter.count
  parameterChart := g.parameter.chart
  sourceNormDomain := g.Omega
  parameterNormDomain := g.Q
  parameterSet := univ
  parameterOpen := univ
  F0 := F0

def parameterFamily : TensorBufferedChartFamily (Fin g.parameter.count) P Ep :=
  tensorChartFamilyOfAtlas g.parameter

def sourceParentPreparation :
    TensorRawCutoffPreparation g.source (sourceCollarNovParentRawProfile g.BS) g.TS g.Ds :=
  sourceCollarNovParentRawPreparation g.source_smooth g.sourcePreparation g.BS_nonneg

def parameterParentPreparation :
    TensorRawCutoffPreparation g.parameter (sourceCollarNovParentRawProfile g.BP) g.TP g.Dp :=
  sourceCollarNovParentRawPreparation g.parameter_smooth g.parameterPreparation g.BP_nonneg

def parameterLocalPreparation :
    TensorLocalRawPreparation g.parameterFamily univ (sourceCollarNovParentRawProfile g.BP) g.TP g.Dp :=
  parameterRound2_localPreparationOfGlobal g.parameter g.parameterParentPreparation univ

theorem sourceParentProfile_nonneg (j : ℕ) : 0 ≤ sourceCollarNovParentRawProfile g.BS j :=
  sourceCollarNovParentRawProfile_nonneg g.BS g.BS_nonneg j

theorem parameterParentProfile_nonneg (j : ℕ) : 0 ≤ sourceCollarNovParentRawProfile g.BP j :=
  sourceCollarNovParentRawProfile_nonneg g.BP g.BP_nonneg j

def samples : (Fin g.source.count × Fin g.parameter.count) → Set (Fin (n+d) → ℝ) :=
  incrementsOriginalEvaluation g.source g.parameter.chart g.Omega g.Q univ

def differentiation : (Fin g.source.count × Fin g.parameter.count) → Set (Fin (n+d) → ℝ) :=
  incrementsOriginalDifferentiation g.source g.parameter.chart

theorem samples_compact (i) : IsCompact (g.samples i) :=
  parameterRound2_originalEvaluation_univ_compact g.source g.parameter.chart g.Omega g.Q
    g.source_compact g.parameter_compact g.source_target g.parameter_target i

theorem samples_subset (i) : g.samples i ⊆ g.differentiation i := fun _ h => h.1

include g in
theorem sourceCompact : CompactSpace M :=
  repair_source_compact_of_original_sampling g.source g.Omega
    g.source_compact g.source_target g.source_sampling

theorem parameter_local_sampling (i) : tensorLocalSamplingCoordinates g.parameterFamily i ⊆ g.Q i :=
  g.parameter_sampling i

variable {m : ℕ}
theorem seed_domains [CompactSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (g : SourceCollarNovSetup (m+1) d M P)
    (hSource : 2 ≤ m+1) (hTarget : (m+1)*((m+1)+1)/2+1 ≤ N)
    (F0 : P × M → EuclideanSpace ℝ (Fin N)) : RepairReferenceSeedDomains (g.seed F0) where
  source_dim := hSource
  target_dim := hTarget
  parameter_open := isOpen_univ
  parameter_compact := isCompact_univ
  parameter_subset := Subset.rfl
  atlas_smooth := g.source_smooth
  parameter_charts_smooth := g.parameter_smooth.chart_mem
  source_norm_subset := g.source_target
  source_inner_norm := by
    intro i x hx
    exact g.source_sampling i (bufferedInner_subset_sampling g.source i
      (bufferedInnerCoordinates_mem g.source i hx))
  parameter_norm_subset := g.parameter_target
  parameter_cover := by
    intro p _
    obtain ⟨i,hi⟩ := g.parameter.cover p
    exact ⟨i,g.parameter.inner_subset i hi,
      g.parameter_sampling i (bufferedInner_subset_sampling g.parameter i
        (bufferedInnerCoordinates_mem g.parameter i hi))⟩

end SourceCollarNovSetup
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.sourceParentPreparation
#print axioms GlobalEmbedding.Continuation.SourceCollarNovSetup.seed_domains
