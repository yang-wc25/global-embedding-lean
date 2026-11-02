import Smoothing.Round4UniformTemplateNativeC3NormalFactory
import Smoothing.Round4NormalCutoffCarrier

/-! An actual normal carrier retains the same slices, ambient coordinate,
normal, and all later jet estimates. Pulling it through the SAME joint chart
preserves the physical point and the true phase-free condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance templateNormalRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance templateNormalSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance templateNormalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance templateNormalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance templateNormalTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance templateNormalTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance templateNormalTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance templateNormalTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

def Round4PhaseNormalAt
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep × M → ℝ) (y : Ep × M) (v : V) : Prop :=
  ∃ nu : normalSpace (I := 𝓙) (F y.1) y.2,
    (nu : V) = v ∧ ‖nu‖ = 1 ∧
    let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi y)).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (y.1,x)) y.2)
    ∀ u w : xi.ker, inner ℝ
      ((trueSecondForm (F y.1) (hF y.1) y.2
        (symmetricSquareProduct (TangentSpace 𝓙 y.2) u.val w.val)) : V) (nu : V) = 0

structure Round4ActualNormalCarrier
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (psi : Ep × M → ℝ) (center : X) (rhoN cF cT : ℝ) where
  slices : Ep → OpenPartialHomeomorph M D
  slices_data : ActualOriginalHostSliceData host b psi slices
  coordinate : Fin N
  normal_smooth : ContDiffOn ℝ ∞
    (actualOriginalUnitFreeNormal F hF slices (EuclideanSpace.single coordinate 1))
    (b.target ∩ ball (b center) rhoN)
  normal_legal : ∀ z ∈ b.target ∩ ball (b center) rhoN,
    Round4PhaseNormalAt (m := m) (N := N) F hF psi (z.1,(slices z.1).symm z.2)
      (actualOriginalUnitFreeNormal F hF slices (EuclideanSpace.single coordinate 1) z)
  normal_jets : ∀ (j : ℕ) (ell Aj Hj : ℝ), 0 < ell → 0 ≤ Aj → 0 ≤ Hj →
    (∀ k ≤ j, ∀ z ∈ b.target ∩ ball (b center) rhoN, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (slices y.1).symm) y.2) z‖ ≤ Aj) →
    (∀ k ≤ j, ∀ z ∈ b.target ∩ ball (b center) rhoN, ell^k*‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (slices y.1).symm)) y.2) z‖ ≤ Hj) →
    ∀ k ≤ j, ∀ z ∈ b.target ∩ ball (b center) rhoN, ell^k*‖iteratedFDeriv ℝ k
      (actualOriginalUnitFreeNormal F hF slices (EuclideanSpace.single coordinate 1)) z‖ ≤
        round4OriginalNormalConstant m N j cF cT Aj Hj (round4AmbientCoordinateReserve N/2) 1
          (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num))


def round4ActualNormalCarrierHostField
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (psi : Ep × M → ℝ) (center : X) (rhoN cF cT : ℝ)
    (data : Round4ActualNormalCarrier F hF host b psi center rhoN cF cT) : X → V :=
  fun z => actualOriginalUnitFreeNormal F hF data.slices (EuclideanSpace.single data.coordinate 1) (b z)

theorem round4_actual_normal_carrier_host_smooth
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (psi : Ep × M → ℝ) (center : X) (rhoN cF cT : ℝ)
    (data : Round4ActualNormalCarrier F hF host b psi center rhoN cF cT)
    (hb : ContDiffOn ℝ ∞ b b.source) :
    ContDiffOn ℝ ∞ (round4ActualNormalCarrierHostField F hF host b psi center rhoN cF cT data)
      (round4NormalCutoffCarrier b center rhoN) :=
  data.normal_smooth.comp (hb.mono inter_subset_left) (round4NormalCutoffCarrier_mapsTo b center rhoN)

theorem round4_actual_normal_carrier_host_point
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (psi : Ep × M → ℝ) (center : X) (rhoN cF cT : ℝ)
    (data : Round4ActualNormalCarrier F hF host b psi center rhoN cF cT)
    (z : X) (hz : z ∈ b.source) :
    (z.1,host.symm z.2) = ((b z).1,(data.slices (b z).1).symm (b z).2) := by
  have hp := data.slices_data.2.2.2.2.2.2.2.2.2.1 (b z) (b.map_source hz)
  change ((b.symm (b z)).1,host.symm (b.symm (b z)).2) = _ at hp
  simpa only [b.left_inv hz] using hp

theorem round4_actual_normal_carrier_host_legal
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (psi : Ep × M → ℝ) (center : X) (rhoN cF cT : ℝ)
    (data : Round4ActualNormalCarrier F hF host b psi center rhoN cF cT)
    (z : X) (hz : z ∈ round4NormalCutoffCarrier b center rhoN) :
    Round4PhaseNormalAt F hF psi (z.1,host.symm z.2)
      (round4ActualNormalCarrierHostField F hF host b psi center rhoN cF cT data z) := by
  have h := data.normal_legal (b z) (round4NormalCutoffCarrier_mapsTo b center rhoN hz)
  exact Eq.mpr (congrArg (fun y => Round4PhaseNormalAt F hF psi y
      (round4ActualNormalCarrierHostField F hF host b psi center rhoN cF cT data z))
    (round4_actual_normal_carrier_host_point F hF host b psi center rhoN cF cT data z hz.1)) h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_normal_carrier_host_smooth
#print axioms GlobalEmbedding.Continuation.round4_actual_normal_carrier_host_legal
