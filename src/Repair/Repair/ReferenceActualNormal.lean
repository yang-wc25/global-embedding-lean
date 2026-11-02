import Repair.EndpointTemplateData
import Smoothing.Round4ActualNormalCarrier

/-!
# Actual Round4 normals on the original compact parameter manifold

The normal is the literal pullback of the existing constructed carrier
normal.  Its domain is the actual product chart preimage of the same
carrier. Openness, coordinate smoothness, unit norm, original normal-space
membership and freeness on the exact host-linear phase kernel are proved.
No normal legality or completed original-normal record is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
private local instance referenceNormalTangentNormed (x : M) : NormedAddCommGroup (TangentSpace I x) := inferInstance
private local instance referenceNormalTangentSpace (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance
private local instance referenceNormalTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace I x) := inferInstance

structure RepairReferenceActualNormal
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ) where
  chart : OpenPartialHomeomorph X X
  center : X
  radius : ℝ
  cF : ℝ
  cT : ℝ
  chart_smooth : ContDiffOn ℝ ∞ chart chart.source
  carrier : Round4ActualNormalCarrier
    (fun p x => seed.F0 (parameterHost.symm p,x)) (fun p => hF (parameterHost.symm p))
    host chart (fun z => xi (host z.2)) center radius cF cT

def repairReferenceActualNormalCoordinates
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ)
    (actual : RepairReferenceActualNormal seed hF parameterHost host xi) : X → V :=
  round4ActualNormalCarrierHostField
    (fun p x => seed.F0 (parameterHost.symm p,x)) (fun p => hF (parameterHost.symm p))
    host actual.chart (fun z => xi (host z.2)) actual.center actual.radius actual.cF actual.cT actual.carrier

def repairReferenceActualNormalCarrier
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ)
    (actual : RepairReferenceActualNormal seed hF parameterHost host xi) : Set X :=
  round4NormalCutoffCarrier actual.chart actual.center actual.radius

def repairReferenceActualNormalField
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ)
    (actual : RepairReferenceActualNormal seed hF parameterHost host xi) (z : P × M) : V :=
  repairReferenceActualNormalCoordinates seed hF parameterHost host xi actual (parameterHost z.1,host z.2)

def repairReferenceActualNormalDomain
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ)
    (actual : RepairReferenceActualNormal seed hF parameterHost host xi) : Set (P × M) :=
  (parameterHost.prod host).source ∩ (parameterHost.prod host) ⁻¹'
    repairReferenceActualNormalCarrier seed hF parameterHost host xi actual

theorem repair_reference_actual_normal_domain_open
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ)
    (actual : RepairReferenceActualNormal seed hF parameterHost host xi) :
    IsOpen (repairReferenceActualNormalDomain seed hF parameterHost host xi actual) :=
  (parameterHost.prod host).isOpen_inter_preimage
    (round4NormalCutoffCarrier_open actual.chart actual.center actual.radius)

theorem repair_reference_actual_normal_coordinates_smooth
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ)
    (actual : RepairReferenceActualNormal seed hF parameterHost host xi) :
    ContDiffOn ℝ ∞ (repairReferenceActualNormalCoordinates seed hF parameterHost host xi actual)
      (repairReferenceActualNormalCarrier seed hF parameterHost host xi actual) :=
  round4_actual_normal_carrier_host_smooth _ _ host actual.chart (fun z => xi (host z.2))
    actual.center actual.radius actual.cF actual.cT actual.carrier actual.chart_smooth

/-- This predicate is literally the original native normal, norm, and
true-second-form kernel condition for the actual host-linear covector. -/
def RepairReferenceHostNormalAt
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (host : OpenPartialHomeomorph M D) (xi : D →L[ℝ] ℝ) (x : M) (v : V) : Prop :=
  ∃ nu : normalSpace («I» := I) F x, (nu : V)=v ∧ ‖nu‖=1 ∧
    ∀ u w : (round4HostPhaseCovector host xi x).ker,
      inner ℝ ((trueSecondForm F hF x
        (symmetricSquareProduct (TangentSpace I x) u.val w.val)) : V) (nu : V)=0

theorem repair_reference_actual_normal_legal
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
    (parameterHost : OpenPartialHomeomorph P Ep) (host : OpenPartialHomeomorph M D)
    (xi : D →L[ℝ] ℝ)
    (actual : RepairReferenceActualNormal seed hF parameterHost host xi)
    (z : P × M) (hz : z ∈ repairReferenceActualNormalDomain seed hF parameterHost host xi actual) :
    RepairReferenceHostNormalAt (fun x => seed.F0 (z.1,x)) (hF z.1) host xi z.2
      (repairReferenceActualNormalField seed hF parameterHost host xi actual z) := by
  have hh := round4_actual_normal_carrier_host_legal
    (fun p x => seed.F0 (parameterHost.symm p,x)) (fun p => hF (parameterHost.symm p))
    host actual.chart (fun y => xi (host y.2)) actual.center actual.radius actual.cF actual.cT
    actual.carrier (parameterHost z.1,host z.2) hz.2
  let v := repairReferenceActualNormalField seed hF parameterHost host xi actual z
  change RepairReferenceHostNormalAt (fun x => seed.F0 (parameterHost.symm (parameterHost z.1),x))
    (hF (parameterHost.symm (parameterHost z.1))) host xi (host.symm (host z.2)) v at hh
  have hx : host.symm (host z.2)=z.2 := host.left_inv hz.1.2
  have hp : parameterHost.symm (parameterHost z.1)=z.1 := parameterHost.left_inv hz.1.1
  have h1 : RepairReferenceHostNormalAt (fun x => seed.F0 (parameterHost.symm (parameterHost z.1),x))
      (hF (parameterHost.symm (parameterHost z.1))) host xi z.2 v := hx ▸ hh
  exact hp ▸ h1

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_actual_normal_domain_open
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_normal_coordinates_smooth
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_normal_legal
