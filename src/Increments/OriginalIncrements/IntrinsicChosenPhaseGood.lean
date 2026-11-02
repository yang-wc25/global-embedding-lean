import Smoothing.Round4ActualHostGoodPhases

/-! Reverse qualitative covariance for the same actual chosen phase.
There is no quantitative auxiliary-norm comparison and no replacement of
the original background norm. The actual chart differential transports
the original good covector to its literal coordinate differential. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation.OriginalIncrements
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance chosenGoodRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance chosenGoodSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

theorem native_good_covector_pullback
    {D E V : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : D ≃L[ℝ] E) (eta : E →L[ℝ] ℝ)
    (B : SymmetricSquare D →L[ℝ] V) (T : SymmetricSquare E →L[ℝ] V)
    (hBT : B=T.comp (symmetricSquareMapL A.toContinuousLinearMap))
    (hGood : LinearSecondFormGoodCovector T.toLinearMap eta.toLinearMap) :
    LinearSecondFormGoodCovector B.toLinearMap (eta.comp A.toContinuousLinearMap).toLinearMap := by
  have hTB : T=B.comp (symmetricSquareMapL A.symm.toContinuousLinearMap) := by
    ext v
    rw [hBT]
    simp only [ContinuousLinearMap.comp_apply,symmetricSquareMapL_apply,
      show symmetricSquareMap A.toContinuousLinearMap
        (symmetricSquareMap A.symm.toContinuousLinearMap v)=v from
          symmetricSquareMap_symm A.symm v]
  exact round4_good_covector_coordinate_to_intrinsic A.symm eta T B hTB hGood

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance chosenGoodTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance chosenGoodTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance chosenGoodTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

theorem original_good_phase_native_operator
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (U : Set X) (hU : IsOpen U)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) U)
    (z : X) (hz : z ∈ U) (hcoord : z.2 ∈ host.target)
    (psi : M → ℝ) (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2))
    (hGood : GoodCovector (F z.1) (hF z.1) (host.symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (host.symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2)))) :
    LinearSecondFormGoodCovector
      (round4ActualPhaseOperatorInChart F (fun _ => host) z).toLinearMap
      (fderiv ℝ (psi ∘ host.symm) z.2).toLinearMap := by
  let A := actualIncrementChartDerivativeEquiv host hhost z.2 hcoord
  let eta := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (host.symm z.2))).toContinuousLinearMap.comp
    (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (host.symm z.2))
  let T := (normalSpace (I := 𝓙) (F z.1) (host.symm z.2)).subtypeL.comp
    (trueSecondFormL (F z.1) (hF z.1) (host.symm z.2))
  have hNormed := (good_covector_iff_normed (F z.1) (hF z.1) (host.symm z.2) eta).mp hGood
  have hTGood : LinearSecondFormGoodCovector T.toLinearMap eta.toLinearMap := by
    apply (linearSecondFormGoodCovector_iff_native_restriction T eta).mpr
    refine ⟨hNormed.1,?_⟩
    intro u v huv
    apply hNormed.2
    apply Subtype.val_injective
    exact huv
  have hBT := round4_actual_phase_operator_chart_transport F hF (fun _ => host) (fun _ => hhost)
    U hU hJoint z hz hcoord
  have hGoodNative := native_good_covector_pullback A eta
    (round4ActualPhaseOperatorInChart F (fun _ => host) z) T hBT hTGood
  have hChain : fderiv ℝ (psi ∘ host.symm) z.2 = eta.comp A.toContinuousLinearMap := by
    have h := mfderiv_comp z.2 hpsi
      ((actual_increment_maximal_chart_mdifferentiable host hhost).mdifferentiableAt_symm hcoord)
    rw [mfderiv_eq_fderiv] at h
    exact h
  rwa [hChain]

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_good_phase_native_operator
