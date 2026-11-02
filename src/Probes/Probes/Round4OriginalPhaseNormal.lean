import Probes.Round4OriginalUniformNormalJets
import Probes.ActualIncrementAdaptedPhaseReserve

/-!
The margin of the SAME adapted phase supplies the transverse reserve in the
dimension-generated normal construction. The result is free on the original
ker(d psi), with no preselected normal and no transverse Gram estimate as
input. One normal and one low-order radius work for every later jet order.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance phaseNormalRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance phaseNormalSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m N : ℕ} {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance phaseNormalFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance phaseNormalFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance phaseNormalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance phaseNormalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance phaseNormalTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance phaseNormalTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance phaseNormalTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

theorem round4_actual_original_phase_normal_before_all_orders
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep → M → ℝ) (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (cF eta C MA MH : ℝ) (hcF : 0 < cF) (heta : 0 < eta) (hC : 0 < C)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hFirst : ∀ z ∈ O, ∀ w : D,
      cF*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2)
    (hpsi : ∀ z ∈ O, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
    (hadapt : ∀ z ∈ O, psi z.1 ((e z.1).symm z.2) = z.2 0)
    (hforward : ∀ z ∈ O,
      ‖(tangentSpaceCastModel 𝓙 (e z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓙 (e z.1) ((e z.1).symm z.2))‖^2 ≤ C)
    (hmargin : ∀ z ∈ O,
      let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
      ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
        ‖covectorRestriction (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2)) xi w‖)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (hdim : (m+1)*(m+2)/2 < N) (x : X) (hx : x ∈ O) :
    let cT := (eta/(C*actualIncrementSortedSymmetricConstant m))^2
    let rho := round4OriginalNormalRadius m N cF cT MA MH
    let S := O ∩ ball x rho
    0 < rho ∧ ∃ i : Fin N,
      let normal := actualOriginalUnitFreeNormal F hF e (EuclideanSpace.single i 1)
      ContDiffOn ℝ ∞ normal S ∧
      (∀ z ∈ S, ∃ nu : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
        (nu : V) = normal z ∧ ‖nu‖ = 1 ∧
        let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
        ∀ u w : xi.ker, inner ℝ
          ((trueSecondForm (F z.1) (hF z.1) ((e z.1).symm z.2)
            (symmetricSquareProduct (TangentSpace 𝓙 ((e z.1).symm z.2)) u.val w.val)) : V)
          (nu : V) = 0) ∧
      ∀ (j : ℕ) (ell Aj Hj : ℝ), 0 < ell → 0 ≤ Aj → 0 ≤ Hj →
        (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
          (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ Aj) →
        (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
          (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ Hj) →
        ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k normal z‖ ≤
          round4OriginalNormalConstant m N j cF cT Aj Hj
            (round4AmbientCoordinateReserve N / 2) 1
            (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num)) := by
  intro cT rho S
  have hcT : 0 < cT := sq_pos_of_pos
    (div_pos heta (mul_pos hC (actualIncrementSortedSymmetricConstant_pos m)))
  let slice := fun p => {y : D | (p,y) ∈ O}
  have hSlice (p : Ep) : IsOpen (slice p) := hO.preimage (continuous_const.prodMk continuous_id)
  have hFrame (z : X) (hz : z ∈ O) (t : Tdata) : cT*‖t‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 t‖^2 :=
    actual_increment_adapted_phase_frame_reserve (F z.1) (hF z.1) (psi z.1)
      (e z.1) (he z.1) (slice z.1) (hSlice z.1) (fun y hy => hcoord (z.1,y) hy)
      z.2 hz (hpsi z hz) (fun y hy => hadapt (z.1,y) hy) eta C heta.le hC
      (hforward z hz) (hmargin z hz) t
  obtain ⟨hrho, i, hsmooth, hnormal, hjets⟩ := round4_actual_original_uniform_normal_before_all_orders
    F hF e he O hO hConv hcoord hJoint cF cT MA MH hcF hcT hMA hMH
    hFirst hFrame hAj hHj hdim x hx
  refine ⟨hrho, i, hsmooth, ?_, hjets⟩
  intro z hz
  obtain ⟨nu, heq, hnorm, hbeta⟩ := hnormal z hz
  refine ⟨nu, heq, hnorm, ?_⟩
  exact actual_increment_phase_free_of_transverse_kernel (F z.1) (hF z.1) (psi z.1)
    (e z.1) (he z.1) (slice z.1) (hSlice z.1) (fun y hy => hcoord (z.1,y) hy)
    z.2 hz.1 (hpsi z hz.1) (fun y hy => hadapt (z.1,y) hy) nu hbeta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_original_phase_normal_before_all_orders
