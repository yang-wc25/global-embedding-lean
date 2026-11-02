import Smoothing.Round4ActualNormalCarrier

/-! A nonzero constant rescaling of the actual phase leaves its literal
spatial kernel unchanged. The same actual unit normal is therefore free for
the hierarchical weighted phase; no new normal is chosen. -/

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

theorem round4_phase_normal_const_smul
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (psi : Ep × M → ℝ) (y : Ep × M) (v : V)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun x => psi (y.1,x)) y.2)
    (a : ℝ) (ha : a ≠ 0) (hNormal : Round4PhaseNormalAt F hF psi y v) :
    Round4PhaseNormalAt F hF (fun z => a • psi z) y v := by
  let d := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi y)).toContinuousLinearMap.comp
    (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (y.1,x)) y.2)
  let da := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (a • psi y)).toContinuousLinearMap.comp
    (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => a • psi (y.1,x)) y.2)
  have hCov : da = a • d := by
    have h := const_smul_mfderiv hpsi a
    ext w
    exact congrArg (fun L => L w) h
  rcases hNormal with ⟨nu,hnu,hunit,hfree⟩
  refine ⟨nu,hnu,hunit,?_⟩
  change ∀ u w : da.ker, inner ℝ
    ((trueSecondForm (F y.1) (hF y.1) y.2
      (symmetricSquareProduct (TangentSpace 𝓙 y.2) u.val w.val)) : V) (nu : V) = 0
  intro u w
  have hker (q : da.ker) : d q.val = 0 := by
    have hh : da q.val = 0 := q.property
    have heval := congrArg (fun L : TangentSpace 𝓙 y.2 →L[ℝ] ℝ => L q.val) hCov
    have hz : a * d q.val = 0 := by
      exact heval.symm.trans hh
    exact (mul_eq_zero.mp hz).resolve_left ha
  exact hfree ⟨u.val,hker u⟩ ⟨w.val,hker w⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_phase_normal_const_smul
