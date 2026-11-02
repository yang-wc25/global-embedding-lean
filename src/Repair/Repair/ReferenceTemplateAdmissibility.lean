import Repair.EndpointTemplateData
import Smoothing.ParameterRound2MetricRegularity

/-!
# Original domain and smoothness records for the constructed template datum

The original atlas and parameter assumptions are kept in the seed.  The
generated primary support follows from the actual product cutoffs; phase
smoothness is derived from the literal host-linear formula; the reference
metric is differentiated as gamma(F0).  The actual normal is a pullback
of the factory's smooth native normal on its true carrier.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "I" => 𝓘(ℝ,D)
local notation "IP" => 𝓘(ℝ,Ep)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

private local instance referenceTemplateProductChart : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
private local instance referenceTemplateProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := IP) (I' := I) (n := ∞) P M

/-- Only the original source/parameter domain assumptions, before any
template phase, coefficient, normal or adapted chart is constructed. -/
structure RepairReferenceSeedDomains (seed : RepairOriginalReferenceSeed (m+1) d N M P) : Prop where
  source_dim : 2 ≤ m+1
  target_dim : (m+1)*((m+1)+1)/2+1 ≤ N
  parameter_open : IsOpen seed.parameterOpen
  parameter_compact : IsCompact seed.parameterSet
  parameter_subset : seed.parameterSet ⊆ seed.parameterOpen
  atlas_smooth : IsSmoothBufferedAtlas seed.atlas
  parameter_charts_smooth : ∀ i, seed.parameterChart i ∈ IsManifold.maximalAtlas IP ∞ P
  source_norm_subset : ∀ i, seed.sourceNormDomain i ⊆ (seed.atlas.chart i).target
  source_inner_norm : ∀ i x, x ∈ seed.atlas.inner i → seed.atlas.chart i x ∈ seed.sourceNormDomain i
  parameter_norm_subset : ∀ i, seed.parameterNormDomain i ⊆ (seed.parameterChart i).target
  parameter_cover : ∀ p ∈ seed.parameterSet, ∃ i,
    p ∈ (seed.parameterChart i).source ∧ seed.parameterChart i p ∈ seed.parameterNormDomain i

variable {Host : Type*} [Fintype Host] {Piece : Host → Type*} [∀ i, Fintype (Piece i)]

theorem repair_original_template_domain
    (seed : RepairOriginalReferenceSeed (m+1) d N M P) (hseed : RepairReferenceSeedDomains seed)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ) (inner : ∀ i, Piece i → P × M → ℝ)
    (normal : (Σ i, Piece i × Edge) → P × M → V)
    (domain : (Σ i, Piece i × Edge) → Set (P × M))
    (hDomain : ∀ a, IsOpen (domain a))
    (hSupport : ∀ a z, z ∈ seed.parameterOpen ×ˢ (univ : Set M) →
      z ∈ tsupport (outer a.1) → z ∈ tsupport (inner a.1 a.2.1) → z ∈ domain a) :
    IncrementsOriginalDomainConditions
      (repairOriginalTemplateData seed host hhost template outer inner normal domain) := by
  let data := repairOriginalTemplateData seed host hhost template outer inner normal domain
  refine {
    source_dim := hseed.source_dim
    target_dim := hseed.target_dim
    parameter_open := hseed.parameter_open
    parameter_compact := hseed.parameter_compact
    parameter_subset := hseed.parameter_subset
    atlas_smooth := hseed.atlas_smooth
    parameter_charts_smooth := hseed.parameter_charts_smooth
    source_norm_subset := hseed.source_norm_subset
    source_inner_norm := hseed.source_inner_norm
    parameter_norm_subset := hseed.parameter_norm_subset
    parameter_cover := hseed.parameter_cover
    primary_open := fun nu => hDomain (repairTemplateIndex (m := m) (Piece := Piece) nu)
    cutoff_support_local := ?_ }
  intro nu z hz
  obtain ⟨w,hw,rfl⟩ := hz
  let a := repairTemplateIndex (m := m) (Piece := Piece) nu
  have hleft : w.val ∈ tsupport (outer a.1) :=
    tsupport_comp_subset_preimage (outer a.1) continuous_subtype_val
      (tsupport_mul_subset_left hw)
  have hright : w.val ∈ tsupport (inner a.1 a.2.1) :=
    tsupport_comp_subset_preimage (inner a.1 a.2.1) continuous_subtype_val
      (tsupport_mul_subset_right hw)
  exact hSupport a w.val w.property hleft hright

theorem repair_original_template_smooth
    (seed : RepairOriginalReferenceSeed (m+1) d N M P) (hseed : RepairReferenceSeedDomains seed)
    (hF : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ seed.F0)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ) (inner : ∀ i, Piece i → P × M → ℝ)
    (normal : (Σ i, Piece i × Edge) → P × M → V)
    (domain : (Σ i, Piece i × Edge) → Set (P × M))
    (hSource : ∀ a z, z ∈ domain a → z.2 ∈ (host a.1).source)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hInner : ∀ i q, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (inner i q))
    (parameterHost : Host → OpenPartialHomeomorph P Ep)
    (hParameterHost : ∀ i, parameterHost i ∈ IsManifold.maximalAtlas IP ∞ P)
    (normalCoordinates : (Σ i, Piece i × Edge) → Ep × D → V)
    (normalCarrier : (Σ i, Piece i × Edge) → Set (Ep × D))
    (hNormalSmooth : ∀ a, ContDiffOn ℝ ∞ (normalCoordinates a) (normalCarrier a))
    (hParameter : ∀ a z, z ∈ domain a ∩ (seed.parameterOpen ×ˢ (univ : Set M)) →
      z.1 ∈ (parameterHost a.1).source)
    (hCarrier : ∀ a z, z ∈ domain a ∩ (seed.parameterOpen ×ˢ (univ : Set M)) →
      (parameterHost a.1 z.1,host a.1 z.2) ∈ normalCarrier a)
    (hNormal : ∀ a z, z ∈ domain a ∩ (seed.parameterOpen ×ˢ (univ : Set M)) →
      normal a z = normalCoordinates a (parameterHost a.1 z.1,host a.1 z.2)) :
    IncrementsOriginalSmoothInputs
      (repairOriginalTemplateData seed host hhost template outer inner normal domain) := by
  let data := repairOriginalTemplateData seed host hhost template outer inner normal domain
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hFp := hF
    rw [modelWithCornersSelf_prod] at hFp
    exact hFp.contMDiffOn
  · intro i
    exact (parameterRound2_inducedMetric_originalCoordinates_contDiffOn seed.atlas seed.parameterChart
      hseed.atlas_smooth hseed.parameter_charts_smooth seed.F0 hF i).mono inter_subset_left
  · intro nu
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    letI : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
    have hh : ContMDiffOn IJ I ∞ (fun z : P × M => host a.1 z.2)
        (domain a ∩ (seed.parameterOpen ×ˢ (univ : Set M))) :=
      (contMDiffOn_of_mem_maximalAtlas (hhost a.1)).comp contMDiff_snd.contMDiffOn
        (fun z hz => hSource a z hz.1)
    exact ((template a.1 a.2.1).covectors a.2.2).contDiff.contMDiff.comp_contMDiffOn hh
  · intro nu
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    exact ((hOuter a.1).mul (hInner a.1 a.2.1)).contMDiffOn
  · intro nu
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    letI : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
    have hh : ContMDiffOn IJ I ∞ (fun z : P × M => host a.1 z.2)
        (domain a ∩ (seed.parameterOpen ×ˢ (univ : Set M))) :=
      (contMDiffOn_of_mem_maximalAtlas (hhost a.1)).comp contMDiff_snd.contMDiffOn
        (fun z hz => hSource a z hz.1)
    have hp : ContMDiffOn IJ IP ∞ (fun z : P × M => parameterHost a.1 z.1)
        (domain a ∩ (seed.parameterOpen ×ˢ (univ : Set M))) :=
      (contMDiffOn_of_mem_maximalAtlas (hParameterHost a.1)).comp contMDiff_fst.contMDiffOn
        (fun z hz => hParameter a z hz)
    have hn : ContMDiffOn 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ (normalCoordinates a) (normalCarrier a) :=
      (hNormalSmooth a).contMDiffOn
    apply (hn.comp (hp.prodMk_space hh) (hCarrier a)).congr
    intro z hz
    exact hNormal a z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_original_template_domain
#print axioms GlobalEmbedding.Continuation.repair_original_template_smooth
