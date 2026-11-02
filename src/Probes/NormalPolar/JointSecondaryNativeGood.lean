import NormalPolar.JointSecondaryGoodCoordinates
import Probes.Round4ActualTemplateField
import Probes.Round3PreparedSymmetricSurjection
import GlobalEmbedding.Offline.GoodCovectorDensity
import Probes.ActualIncrementChartMarginReserve

/-! The actual native phase operator is the original true second form on
the whole binary symmetric quotient, with the true tangent chart derivative
and ambient normal inclusion. Consequently native Good and original
GoodCovector are equivalent for every actual covector, not just an adapted
first-coordinate row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped TensorProduct Topology ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance nativeGoodRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance nativeGoodSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

theorem jointSecondary_symmetric_linear_ext_basis {m : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (L R : SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →ₗ[ℝ] V)
    (h : ∀ i j, L (symmetricSquareProduct _ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      R (symmetricSquareProduct _ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) : L = R := by
  let D := EuclideanSpace ℝ (Fin (m+1))
  have hexp (v : D) : v = ∑ i : Fin (m+1), (v i) • EuclideanSpace.single i 1 := by
    ext i
    simp [D,Pi.single_apply,eq_comm]
  apply (symmetricSquareRelations D).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change L (symmetricSquareProduct D v w) = R (symmetricSquareProduct D v w)
  rw [hexp v,hexp w]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun t => w j • t)
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun t => v i • t) (h i j)

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)

def jointSecondaryNativePhaseOperator (F : M → V) (e : OpenPartialHomeomorph M D)
    (y : D) : SymmetricSquare D →L[ℝ] V :=
  round4ActualPhaseOperatorInChart (fun _ : Z => F) (fun _ => e) (0,y)

def jointSecondaryNativeTangentMap (e : OpenPartialHomeomorph M D) (y : D) :
    D →L[ℝ] TangentSpace IM (e.symm y) :=
  (mfderiv IM IM e.symm y).comp (tangentSpaceCastModel IM y).symm.toContinuousLinearMap

theorem jointSecondary_native_operator_true_form
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (y : D) (hy : y ∈ e.target) :
    (jointSecondaryNativePhaseOperator F e y).toLinearMap =
      (((normalSpace (I := IM) F (e.symm y)).subtype).comp (trueSecondForm F hF (e.symm y))).comp
        (symmetricSquareLinearMap (jointSecondaryNativeTangentMap e y).toLinearMap) := by
  have hFs : ContDiffOn ℝ ∞ (F ∘ e.symm) e.target :=
    (hF.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  have hJoint : ContDiffOn ℝ ∞ (fun z : Z × D => F (e.symm z.2)) (univ ×ˢ e.target) :=
    hFs.comp contDiffOn_snd (fun z hz => hz.2)
  apply jointSecondary_symmetric_linear_ext_basis
  intro i j
  have hr := round4_actual_phase_operator_original_rows (fun _ : Z => F) (fun _ => hF)
    (fun _ => e) (fun _ => he) (univ ×ˢ e.target) (isOpen_univ.prod e.open_target)
    hJoint (0,y) ⟨mem_univ _,hy⟩ hy i j
  change _ = ((trueSecondForm F hF (e.symm y))
    (symmetricSquareLinearMap (jointSecondaryNativeTangentMap e y).toLinearMap
      (symmetricSquareProduct D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) : V)
  rw [round3_prepared_symmetric_map_product]
  exact hr

theorem jointSecondary_native_good_iff
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (y : D) (hy : y ∈ e.target) (xi : TangentSpace IM (e.symm y) →L[ℝ] ℝ) :
    LinearSecondFormGoodCovector (jointSecondaryNativePhaseOperator F e y).toLinearMap
      (xi.comp (jointSecondaryNativeTangentMap e y)).toLinearMap ↔
      GoodCovector F hF (e.symm y) xi := by
  rw [jointSecondary_native_operator_true_form F hF e he y hy]
  let L : D ≃ₗ[ℝ] TangentSpace IM (e.symm y) :=
    ((tangentSpaceCastModel IM y).symm.trans
      ((actual_increment_maximal_chart_mdifferentiable e he).symm.mfderiv hy)).toLinearEquiv
  exact (jointSecondary_good_pullback_equiv
    (((normalSpace (I := IM) F (e.symm y)).subtype).comp (trueSecondForm F hF (e.symm y)))
    L xi.toLinearMap).trans
      ((jointSecondary_good_injective_codomain (trueSecondForm F hF (e.symm y))
        (normalSpace (I := IM) F (e.symm y)).subtype Subtype.val_injective xi.toLinearMap).trans
        (goodCovector_iff_linearSecondFormGoodCovector F hF (e.symm y) xi).symm)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_native_operator_true_form
#print axioms GlobalEmbedding.Continuation.jointSecondary_native_good_iff
