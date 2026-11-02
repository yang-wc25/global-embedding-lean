import Repair.ReferenceChartCutoffExtension
import Repair.ReferenceCarrierTemplateData

/-!
# The actual carrier data with genuinely global refinement cutoffs

Each local refinement function is extended by zero through its actual
parameter/source product chart.  Its factory support containment supplies
global smoothness and the original primary-domain support condition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped ContDiff Topology BigOperators
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
local notation "I" => 𝓘(ℝ,D)
local notation "IP" => 𝓘(ℝ,Ep)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance zeroCarrierProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance zeroCarrierTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance zeroCarrierProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := IP) (I' := I) (n := ∞) P M

variable {Host : Type*} [Fintype Host] {Piece : Host → Type*} [∀ i, Fintype (Piece i)]

theorem repair_reference_product_chart_smooth
    (parameterHost : OpenPartialHomeomorph P Ep)
    (hParameterHost : parameterHost ∈ IsManifold.maximalAtlas IP ∞ P)
    (host : OpenPartialHomeomorph M D)
    (hHost : host ∈ IsManifold.maximalAtlas I ∞ M) :
    ContMDiffOn IJ 𝓘(ℝ,Ep × D) ∞ (parameterHost.prod host) (parameterHost.prod host).source := by
  letI : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
  have hp : ContMDiffOn IJ IP ∞ (fun z : P × M => parameterHost z.1)
      (parameterHost.prod host).source :=
    (contMDiffOn_of_mem_maximalAtlas hParameterHost).comp contMDiff_fst.contMDiffOn
      (fun _ hz => hz.1)
  have hh : ContMDiffOn IJ I ∞ (fun z : P × M => host z.2)
      (parameterHost.prod host).source :=
    (contMDiffOn_of_mem_maximalAtlas hHost).comp contMDiff_snd.contMDiffOn
      (fun _ hz => hz.2)
  exact hp.prodMk_space hh

def repairOriginalZeroExtendedCarrierTemplateData
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ)
    (parameterHost : Host → OpenPartialHomeomorph P Ep)
    (eta : ∀ i, Piece i → Ep × D → ℝ)
    (actual : ∀ a : (Σ i, Piece i × Edge), RepairReferenceActualNormal seed hF
      (parameterHost a.1) (host a.1) ((template a.1 a.2.1).covectors a.2.2)) :
    IncrementsOriginalNativeData (m+1) d N M P :=
  repairOriginalCarrierTemplateData seed hF host hhost template outer
    (fun i q => repairReferenceChartCutoff ((parameterHost i).prod (host i)) (eta i q))
    parameterHost actual

/-- Actual local smoothness and compact target support now produce all
original admissibility records for the concrete zero-extended data. -/
theorem repair_original_zero_extended_carrier_admissibility
    (seed : RepairOriginalReferenceSeed (m+1) d N M P) (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ seed.F0)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (parameterHost : Host → OpenPartialHomeomorph P Ep)
    (hParameterHost : ∀ i, parameterHost i ∈ IsManifold.maximalAtlas IP ∞ P)
    (eta : ∀ i, Piece i → Ep × D → ℝ)
    (hEta : ∀ i q, ContDiff ℝ ∞ (eta i q))
    (hCompact : ∀ i q, IsCompact (tsupport (eta i q)))
    (hTarget : ∀ i q, tsupport (eta i q) ⊆ ((parameterHost i).prod (host i)).target)
    (actual : ∀ a : (Σ i, Piece i × Edge), RepairReferenceActualNormal seed hF
      (parameterHost a.1) (host a.1) ((template a.1 a.2.1).covectors a.2.2))
    (hCarrier : ∀ a : (Σ i, Piece i × Edge), tsupport (eta a.1 a.2.1) ⊆
      repairReferenceActualNormalCarrier seed hF (parameterHost a.1) (host a.1)
        ((template a.1 a.2.1).covectors a.2.2) (actual a)) :
    let data := repairOriginalZeroExtendedCarrierTemplateData seed hF host hhost template outer
      parameterHost eta actual
    ∃ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
      IncrementsOriginalFreeNormalConditions data hd hs := by
  intro data
  apply repair_original_carrier_template_admissibility seed hseed hFjoint hF host hhost template outer
    (fun i q => repairReferenceChartCutoff ((parameterHost i).prod (host i)) (eta i q)) hOuter
    (fun i q => repair_reference_chart_cutoff_smooth IJ _ _
      (repair_reference_product_chart_smooth (parameterHost i) (hParameterHost i) (host i) (hhost i))
      (hEta i q) (hCompact i q) (hTarget i q))
    parameterHost hParameterHost actual
  intro a z _ _ hz
  have hs := (repair_reference_chart_cutoff_support ((parameterHost a.1).prod (host a.1))
    (eta a.1 a.2.1) (hCompact a.1 a.2.1) (hTarget a.1 a.2.1)).2 hz
  exact ⟨hs.1, hCarrier a hs.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_product_chart_smooth
#print axioms GlobalEmbedding.Continuation.repair_original_zero_extended_carrier_admissibility
