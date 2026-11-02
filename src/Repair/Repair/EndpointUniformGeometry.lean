import Repair.EndpointCompactParameterGeometry
import Repair.EndpointTemplateData
import Repair.ReferenceTemplateAdmissibility
import Repair.EndpointSourceCompactness
import Smoothing.ParameterRound2PreparedGeometry

/-! Original fixed source/parameter geometry, before the reference map.
Only actual atlases, raw preparations, fixed norm domains and fixed convex
collars occur. Neither phase data nor repair outputs are stored here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

structure RepairOriginalUniformGeometry (n d : ℕ) (M P : Type*)
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
  sourceCollars : RepairCompactChartCollars source sourcePreparation.raw Omega
  parameterCollars : RepairCompactChartCollars parameter parameterPreparation.raw Q

namespace RepairOriginalUniformGeometry
variable (g : RepairOriginalUniformGeometry n d M P)

def seed (F0 : P × M → EuclideanSpace ℝ (Fin N)) : RepairOriginalReferenceSeed n d N M P where
  atlas := g.source
  sourceNormDomain := g.Omega
  parameterCount := g.parameter.count
  parameterChart := g.parameter.chart
  parameterNormDomain := g.Q
  parameterSet := univ
  parameterOpen := univ
  F0 := F0

def parameterFamily : TensorBufferedChartFamily (Fin g.parameter.count) P Ep :=
  tensorChartFamilyOfAtlas g.parameter

def parameterLocalPreparation : TensorLocalRawPreparation g.parameterFamily univ g.BP g.TP g.Dp :=
  parameterRound2_localPreparationOfGlobal g.parameter g.parameterPreparation univ

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

variable {m : ℕ}
theorem seed_domains [CompactSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
    (g : RepairOriginalUniformGeometry (m+1) d M P)
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
    exact g.source_sampling i (bufferedInner_subset_sampling g.source i (bufferedInnerCoordinates_mem g.source i hx))
  parameter_norm_subset := g.parameter_target
  parameter_cover := by
    intro p _
    obtain ⟨i,hi⟩ := g.parameter.cover p
    exact ⟨i,g.parameter.inner_subset i hi,
      g.parameter_sampling i (bufferedInner_subset_sampling g.parameter i
        (bufferedInnerCoordinates_mem g.parameter i hi))⟩

end RepairOriginalUniformGeometry

/-- Compact parameters supply every fixed geometric datum, with no
reference map or target metric present during the choices. Source
geometry is the original fixed buffered geometry of Setup:uniform. -/
theorem repair_original_geometry_with_compact_parameters [CompactSpace P] [T2Space P]
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (BS TS : ℕ → ℝ) (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (Ds : ℕ) (RS : TensorRawCutoffPreparation A BS TS Ds)
    (Omega : Fin A.count → Set D) (hCompact : ∀ i, IsCompact (Omega i))
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (collars : RepairCompactChartCollars A RS.raw Omega) :
    ∃ g : RepairOriginalUniformGeometry n d M P,
      g.source=A ∧ g.BS=BS ∧ g.TS=TS ∧ g.Ds=Ds ∧
      HEq g.sourcePreparation.raw RS.raw ∧ HEq g.Omega Omega := by
  obtain ⟨B,hB,BP,TP,hBP,hTP,RP,Q,hQ,⟨CP⟩⟩ :=
    repair_compact_manifold_prepared_collars (E := Ep) (X := P)
  exact ⟨{
    source := A
    parameter := B
    source_smooth := hA
    parameter_smooth := hB
    BS := BS
    TS := TS
    BP := BP
    TP := TP
    BS_nonneg := hBS
    TS_nonneg := hTS
    BP_nonneg := hBP
    TP_nonneg := hTP
    Ds := Ds
    Dp := B.supportDegree
    sourcePreparation := RS
    parameterPreparation := RP
    Omega := Omega
    Q := Q
    source_compact := hCompact
    parameter_compact := fun i => (hQ i).1
    source_target := hTarget
    parameter_target := fun i => (hQ i).2.1
    source_sampling := hSampling
    parameter_sampling := fun i => subset_closure.trans (hQ i).2.2
    sourceCollars := collars
    parameterCollars := CP },rfl,rfl,rfl,rfl,HEq.rfl,HEq.rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairOriginalUniformGeometry.seed_domains
#print axioms GlobalEmbedding.Continuation.repair_original_geometry_with_compact_parameters
