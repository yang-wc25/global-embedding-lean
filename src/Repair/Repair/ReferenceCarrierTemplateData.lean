import Repair.ReferenceActualNormal
import Repair.ReferenceTemplateAdmissibility
import Repair.EndpointPositiveNeighborhood

/-!
# The native reference datum with the actual constructed free normals

The field and primary domain are defined from each Round4 normal carrier,
then all original domain/smooth/unit/free conditions are produced.  The
input contains original atlas data, actual cutoff fields and actual carrier
objects; it contains no original admissibility or normal-output predicate.
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
private local instance carrierTemplateProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance carrierTemplateProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := IP) (I' := I) (n := ∞) P M

variable {Host : Type*} [Fintype Host] {Piece : Host → Type*} [∀ i, Fintype (Piece i)]

def repairOriginalCarrierTemplateData
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ) (inner : ∀ i, Piece i → P × M → ℝ)
    (parameterHost : Host → OpenPartialHomeomorph P Ep)
    (actual : ∀ a : (Σ i, Piece i × Edge), RepairReferenceActualNormal seed hF
      (parameterHost a.1) (host a.1) ((template a.1 a.2.1).covectors a.2.2)) :
    IncrementsOriginalNativeData (m+1) d N M P :=
  repairOriginalTemplateData seed host hhost template outer inner
    (fun a => repairReferenceActualNormalField seed hF (parameterHost a.1) (host a.1)
      ((template a.1 a.2.1).covectors a.2.2) (actual a))
    (fun a => repairReferenceActualNormalDomain seed hF (parameterHost a.1) (host a.1)
      ((template a.1 a.2.1).covectors a.2.2) (actual a))

theorem repair_original_carrier_template_admissibility
    (seed : RepairOriginalReferenceSeed (m+1) d N M P) (hseed : RepairReferenceSeedDomains seed)
    (hFjoint : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ seed.F0)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas I ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ) (inner : ∀ i, Piece i → P × M → ℝ)
    (hOuter : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (outer i))
    (hInner : ∀ i q, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (inner i q))
    (parameterHost : Host → OpenPartialHomeomorph P Ep)
    (hParameterHost : ∀ i, parameterHost i ∈ IsManifold.maximalAtlas IP ∞ P)
    (actual : ∀ a : (Σ i, Piece i × Edge), RepairReferenceActualNormal seed hF
      (parameterHost a.1) (host a.1) ((template a.1 a.2.1).covectors a.2.2))
    (hSupport : ∀ a z, z ∈ seed.parameterOpen ×ˢ (univ : Set M) →
      z ∈ tsupport (outer a.1) → z ∈ tsupport (inner a.1 a.2.1) →
      z ∈ repairReferenceActualNormalDomain seed hF (parameterHost a.1) (host a.1)
        ((template a.1 a.2.1).covectors a.2.2) (actual a)) :
    let data := repairOriginalCarrierTemplateData seed hF host hhost template outer inner parameterHost actual
    ∃ (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data),
      IncrementsOriginalFreeNormalConditions data hd hs := by
  intro data
  let normal := fun a : (Σ i, Piece i × Edge) =>
    repairReferenceActualNormalField seed hF (parameterHost a.1) (host a.1)
      ((template a.1 a.2.1).covectors a.2.2) (actual a)
  let domain := fun a : (Σ i, Piece i × Edge) =>
    repairReferenceActualNormalDomain seed hF (parameterHost a.1) (host a.1)
      ((template a.1 a.2.1).covectors a.2.2) (actual a)
  have hd : IncrementsOriginalDomainConditions data :=
    repair_original_template_domain seed hseed host hhost template outer inner normal domain
      (fun a => repair_reference_actual_normal_domain_open seed hF (parameterHost a.1) (host a.1)
        ((template a.1 a.2.1).covectors a.2.2) (actual a)) hSupport
  have hs : IncrementsOriginalSmoothInputs data :=
    repair_original_template_smooth seed hseed hFjoint host hhost template outer inner normal domain
      (fun a z hz => hz.1.2) hOuter hInner parameterHost hParameterHost
      (fun a => repairReferenceActualNormalCoordinates seed hF (parameterHost a.1) (host a.1)
        ((template a.1 a.2.1).covectors a.2.2) (actual a))
      (fun a => repairReferenceActualNormalCarrier seed hF (parameterHost a.1) (host a.1)
        ((template a.1 a.2.1).covectors a.2.2) (actual a))
      (fun a => repair_reference_actual_normal_coordinates_smooth seed hF (parameterHost a.1) (host a.1)
        ((template a.1 a.2.1).covectors a.2.2) (actual a))
      (fun a z hz => hz.1.1.1) (fun a z hz => hz.1.2) (fun _ _ _ => rfl)
  have hlegal (nu : Fin data.primaryCount) (z : P × M)
      (hz : z ∈ data.primaryDomain nu ∩ incrementsOriginalParameterRegion data) :=
    repair_reference_actual_normal_legal seed hF
      (parameterHost (repairTemplateIndex (m := m) (Piece := Piece) nu).1)
      (host (repairTemplateIndex (m := m) (Piece := Piece) nu).1)
      ((template (repairTemplateIndex (m := m) (Piece := Piece) nu).1
        (repairTemplateIndex (m := m) (Piece := Piece) nu).2.1).covectors
          (repairTemplateIndex (m := m) (Piece := Piece) nu).2.2)
      (actual (repairTemplateIndex (m := m) (Piece := Piece) nu)) z hz.1
  refine ⟨hd,hs,?_,?_,?_⟩
  · intro nu z hz
    obtain ⟨v,hv,hn,_⟩ := hlegal nu z hz
    change ‖normal (repairTemplateIndex (m := m) (Piece := Piece) nu) z‖=1
    exact (congrArg (fun w : V => ‖w‖) hv).symm.trans hn
  · intro nu z hz
    obtain ⟨v,hv,_,_⟩ := hlegal nu z hz
    change normal (repairTemplateIndex (m := m) (Piece := Piece) nu) z ∈ _
    exact Eq.mp (congrArg (fun w : V => w ∈ normalSpace («I» := I)
      (fun x => seed.F0 (z.1,x)) z.2) hv) v.property
  · intro nu z hz u v
    obtain ⟨normalValue,hnormal,_,hfree⟩ := hlegal nu z hz
    change Inner.inner ℝ ((trueSecondForm (fun x => seed.F0 (z.1,x)) (hF z.1) z.2
      (symmetricSquareProduct (TangentSpace I z.2) u.val v.val)) : V)
      (normal (repairTemplateIndex (m := m) (Piece := Piece) nu) z)=0
    exact (congrArg (fun w : V => Inner.inner ℝ
      ((trueSecondForm (fun x => seed.F0 (z.1,x)) (hF z.1) z.2
        (symmetricSquareProduct (TangentSpace I z.2) u.val v.val)) : V) w) hnormal).symm.trans
      (hfree u v)

/-- Changing only the now-constructed positive fiber neighborhood preserves
all actual original domain, smoothness and free-normal records. -/
theorem repair_reference_positive_admissibility
    (data : IncrementsOriginalNativeData (m+1) d N M P) (rho : ℝ)
    (hd : IncrementsOriginalDomainConditions data) (hs : IncrementsOriginalSmoothInputs data)
    (hn : IncrementsOriginalFreeNormalConditions data hd hs) :
    ∃ (hd' : IncrementsOriginalDomainConditions (repairReferencePositiveData data rho))
      (hs' : IncrementsOriginalSmoothInputs (repairReferencePositiveData data rho)),
      IncrementsOriginalFreeNormalConditions (repairReferencePositiveData data rho) hd' hs' := by
  let hd' : IncrementsOriginalDomainConditions (repairReferencePositiveData data rho) := { hd with }
  let hs' : IncrementsOriginalSmoothInputs (repairReferencePositiveData data rho) := { hs with }
  exact ⟨hd',hs',{ hn with }⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_original_carrier_template_admissibility
#print axioms GlobalEmbedding.Continuation.repair_reference_positive_admissibility
