import GlobalEmbedding.Offline.JointGoodCovectorOpen
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Bounded

/-! A genuine compact carrier supplies a uniform radius in the original
Good predicate. Both the actual second-form operator and actual covector
are allowed to vary. No common cone or completed mixed-Good premise is
assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Metric
open scoped TensorProduct Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance compactGoodRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance compactGoodSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

theorem jointSecondary_compact_actual_good_radius
    {X E V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : X → SymmetricSquare E →L[ℝ] V) (xi : X → E →L[ℝ] ℝ)
    (K : Set X) (hK : IsCompact K) (hB : ContinuousOn B K) (hxi : ContinuousOn xi K)
    (hgood : ∀ x ∈ K, LinearSecondFormGoodCovector (B x).toLinearMap (xi x).toLinearMap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ x ∈ K, ∀ eta : E →L[ℝ] ℝ, ‖eta-xi x‖ < epsilon →
        LinearSecondFormGoodCovector (B x).toLinearMap eta.toLinearMap := by
  let C := (fun x => (B x,xi x)) '' K
  have hC : IsCompact C := hK.image_of_continuousOn (hB.prodMk hxi)
  have hCG : C ⊆ {p : (SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] ℝ) |
      LinearSecondFormGoodCovector p.1.toLinearMap p.2.toLinearMap} := by
    rintro _ ⟨x,hx,rfl⟩
    exact hgood x hx
  obtain ⟨epsilon,he,hthick⟩ := hC.exists_thickening_subset_open
    (isOpen_joint_actual_good_covectors (E := E) (F := V)) hCG
  refine ⟨epsilon,he,?_⟩
  intro x hx eta heta
  apply hthick (a := (B x,eta))
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(B x,xi x),⟨x,hx,rfl⟩,?_⟩
  rw [dist_eq_norm]
  change max ‖B x-B x‖ ‖eta-xi x‖ < epsilon
  simpa only [sub_self,norm_zero,max_eq_right (norm_nonneg _)] using heta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_compact_actual_good_radius
