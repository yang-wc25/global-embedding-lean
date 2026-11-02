import OriginalIncrements.IntrinsicChosenPhaseGood
import GlobalEmbedding.Paper.SaturationEuclideanModel

/-! Qualitative chart covariance using only the original algebraic symmetric
square. No tangent inner product, RiemannianBundle, native margin or
auxiliary-norm comparison is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle
open scoped ContDiff TensorProduct Topology
namespace GlobalEmbedding.Continuation.OriginalIncrements

private theorem algebraic_square_product
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (v w : E) :
    symmetricSquareLinearMap L (symmetricSquareProduct E v w) =
      symmetricSquareProduct F (L v) (L w) :=
  symmetricBilinearDescend_product _ _ v w

theorem algebraic_good_covector_pullback
    {D E V : Type*}
    [AddCommGroup D] [Module ℝ D] [AddCommGroup E] [Module ℝ E]
    [AddCommGroup V] [Module ℝ V]
    (A : D ≃ₗ[ℝ] E) (eta : E →ₗ[ℝ] ℝ)
    (B : SymmetricSquare D →ₗ[ℝ] V) (T : SymmetricSquare E →ₗ[ℝ] V)
    (hBT : B=T.comp (symmetricSquareLinearMap A.toLinearMap))
    (hGood : LinearSecondFormGoodCovector T eta) :
    LinearSecondFormGoodCovector B (eta.comp A.toLinearMap) := by
  let xi := eta.comp A.toLinearMap
  let e : xi.ker ≃ₗ[ℝ] eta.ker :=
    { toFun := fun v => ⟨A v,v.property⟩
      invFun := fun v => ⟨A.symm v,by
        change eta (A (A.symm v))=0
        simpa only [A.apply_symm_apply] using (show eta (v : E)=0 from v.property)⟩
      left_inv := fun v => Subtype.ext (A.symm_apply_apply v)
      right_inv := fun v => Subtype.ext (A.apply_symm_apply v)
      map_add' := fun v w => Subtype.ext (A.map_add v w)
      map_smul' := fun c v => Subtype.ext (A.map_smul c v) }
  let e2 := saturationSymmetricSquareEquiv e
  have hComm : (symmetricSquareLinearMap A.toLinearMap).comp
      (symmetricSquareLinearMap xi.ker.subtype) =
      (symmetricSquareLinearMap eta.ker.subtype).comp e2.toLinearMap := by
    apply (symmetricSquareRelations xi.ker).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change symmetricSquareLinearMap A.toLinearMap
      (symmetricSquareLinearMap xi.ker.subtype (symmetricSquareProduct xi.ker v w)) =
      symmetricSquareLinearMap eta.ker.subtype
        (saturationSymmetricSquareEquiv e (symmetricSquareProduct xi.ker v w))
    rw [algebraic_square_product,algebraic_square_product,
      saturationSymmetricSquareEquiv_product,algebraic_square_product]
    rfl
  refine ⟨?_,?_⟩
  · intro hzero
    apply hGood.1
    ext v
    have h := congrArg (fun L : D →ₗ[ℝ] ℝ => L (A.symm v)) hzero
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,A.apply_symm_apply,
      LinearMap.zero_apply] using h
  · intro u v huv
    apply e2.injective
    apply hGood.2
    have hRest : B.comp (symmetricSquareLinearMap xi.ker.subtype) =
        (T.comp (symmetricSquareLinearMap eta.ker.subtype)).comp e2.toLinearMap := by
      rw [hBT,LinearMap.comp_assoc,hComm,← LinearMap.comp_assoc]
    change (T.comp (symmetricSquareLinearMap eta.ker.subtype)) (e2 u) =
      (T.comp (symmetricSquareLinearMap eta.ker.subtype)) (e2 v)
    exact (congrArg (fun L : SymmetricSquare xi.ker →ₗ[ℝ] V => L u) hRest).symm.trans
      (huv.trans (congrArg (fun L : SymmetricSquare xi.ker →ₗ[ℝ] V => L v) hRest))

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

private theorem actual_phase_operator_algebraic_transport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U : Set X) (hU : IsOpen U)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) U)
    (z : X) (hz : z∈U) (hcoord : z.2∈host.target) :
    (round4ActualPhaseOperatorInChart F (fun _=>host) z).toLinearMap =
      ((normalSpace (I := 𝓙) (F z.1) (host.symm z.2)).subtype.comp
        (trueSecondForm (F z.1) (hF z.1) (host.symm z.2))).comp
      (symmetricSquareLinearMap
        (actualIncrementChartDerivativeEquiv host hhost z.2 hcoord).toLinearEquiv.toLinearMap) := by
  let A := actualIncrementChartDerivativeEquiv host hhost z.2 hcoord
  apply (symmetricSquareRelations D).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change round4ActualPhaseOperatorInChart F (fun _=>host) z (symmetricSquareProduct D v w) =
    (trueSecondForm (F z.1) (hF z.1) (host.symm z.2)
      (symmetricSquareLinearMap A.toLinearEquiv.toLinearMap (symmetricSquareProduct D v w)) : V)
  rw [algebraic_square_product,round4_actual_phase_operator_product F (fun _=>host) U hU hJoint z hz]
  have he2 : host ∈ IsManifold.maximalAtlas 𝓙 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hhost
  have hcv (v : D) : mfderiv 𝓙 𝓙 host (host.symm z.2) (A v)=v := A.symm_apply_apply v
  rw [← trueSecondForm_chart (F z.1) (hF z.1) (host.symm z.2) host he2 (host.map_target hcoord)]
  change (normalSpace (I := 𝓙) (F z.1) (host.symm z.2)).starProjection
    (fderiv ℝ (fderiv ℝ (F z.1 ∘ host.symm)) z.2 v w) =
    (normalSpace (I := 𝓙) (F z.1) (host.symm z.2)).starProjection
      (fderiv ℝ (fderiv ℝ (F z.1 ∘ host.symm)) (host (host.symm z.2))
        (mfderiv 𝓙 𝓙 host (host.symm z.2) (A v))
        (mfderiv 𝓙 𝓙 host (host.symm z.2) (A w)))
  rw [hcv,hcv,host.right_inv hcoord]

/-- Original algebraic Good gives Good for the SAME actual coordinate phase
operator and literal coordinate phase differential, with no extra geometry. -/
theorem original_good_phase_native_operator_algebraic
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U : Set X) (hU : IsOpen U)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) U)
    (z : X) (hz : z∈U) (hcoord : z.2∈host.target)
    (psi : M → ℝ)
    (hGood : GoodCovector (F z.1) (hF z.1) (host.symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (host.symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2)))) :
    LinearSecondFormGoodCovector
      (round4ActualPhaseOperatorInChart F (fun _=>host) z).toLinearMap
      (fderiv ℝ (psi ∘ host.symm) z.2).toLinearMap := by
  let A := actualIncrementChartDerivativeEquiv host hhost z.2 hcoord
  let eta := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (host.symm z.2))).toContinuousLinearMap.comp
    (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2))
  let T := (normalSpace (I := 𝓙) (F z.1) (host.symm z.2)).subtype.comp
    (trueSecondForm (F z.1) (hF z.1) (host.symm z.2))
  have hT : LinearSecondFormGoodCovector T eta.toLinearMap := by
    refine ⟨by exact_mod_cast hGood.1,?_⟩
    intro u v huv
    apply hGood.2
    apply Subtype.val_injective
    exact huv
  have hBT := actual_phase_operator_algebraic_transport F hF host hhost U hU hJoint z hz hcoord
  have hNative := algebraic_good_covector_pullback A.toLinearEquiv eta.toLinearMap
    (round4ActualPhaseOperatorInChart F (fun _=>host) z).toLinearMap T hBT hT
  have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2) := by
    by_contra h
    apply hGood.1
    rw [mfderiv_zero_of_not_mdifferentiableAt h,ContinuousLinearMap.comp_zero]
  have hChain : fderiv ℝ (psi ∘ host.symm) z.2 = eta.comp A.toContinuousLinearMap := by
    have h := mfderiv_comp z.2 hpsi
      ((actual_increment_maximal_chart_mdifferentiable host hhost).mdifferentiableAt_symm hcoord)
    rw [mfderiv_eq_fderiv] at h
    exact h
  rw [hChain]
  exact hNative

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.algebraic_good_covector_pullback
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_good_phase_native_operator_algebraic
