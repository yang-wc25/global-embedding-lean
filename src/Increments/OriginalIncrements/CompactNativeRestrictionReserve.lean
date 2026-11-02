import GlobalEmbedding.Offline.JointGoodCovectorReserves
import Repair.IncrementUniformSignedReserve

/-! A compact family of actual good pairs has a positive restriction
reserve on an actual open neighborhood. Kernels move literally with the
given covectors, and use the existing canonical symmetric-square norm.
The constants are chosen for this fixed family; no uniformity across
uncontrolled changing good covectors is asserted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric
open scoped TensorProduct Topology Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance compactNativeRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance compactNativeSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {X E V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_native_restriction_reserve
    (B : X → SymmetricSquare E →L[ℝ] V) (xi : X → E →L[ℝ] ℝ)
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hB : ContinuousOn B U) (hxi : ContinuousOn xi U)
    (hGood : ∀ x ∈ K, LinearSecondFormGoodCovector (B x).toLinearMap (xi x).toLinearMap) :
    ∃ (kappa : ℝ) (O : Set X), 0 < kappa ∧ IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      ∀ x ∈ O, ∀ v, kappa*‖v‖ ≤ ‖covectorRestriction (B x) (xi x) v‖ := by
  have hLocal (x : K) := actual_good_covector_product_ball_reserves (B x.val) (xi x.val)
    (hGood x.val x.property)
  choose mu hmu eps heps Q hQ hBQ hControl using hLocal
  let W (x : K) : Set X := U ∩ (fun y => (B y,xi y)) ⁻¹' (Q x ×ˢ ball (xi x.val) (eps x))
  have hW (x : K) : IsOpen (W x) :=
    (hB.prodMk hxi).isOpen_inter_preimage hU ((hQ x).prod isOpen_ball)
  have hxW (x : K) : x.val ∈ W x :=
    ⟨hKU x.property,hBQ x,mem_ball_self (heps x)⟩
  have hCover : K ⊆ ⋃ x : K, W x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxW ⟨x,hx⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover W hW hCover
  obtain ⟨kappa,hkappa,hkappaLe⟩ := finite_positive_common_lower_bound
    (fun x : s => mu x.val) (fun x => hmu x.val)
  let O := ⋃ x ∈ s, W x
  have hO : IsOpen O := isOpen_iUnion (fun x => isOpen_iUnion (fun _ => hW x))
  have hOU : O ⊆ U := by
    intro y hy
    obtain ⟨x,hxs,hyx⟩ := mem_iUnion₂.mp hy
    exact hyx.1
  refine ⟨kappa,O,hkappa,hO,hs,hOU,?_⟩
  intro y hy v
  obtain ⟨x,hxs,hyx⟩ := mem_iUnion₂.mp hy
  have hNear : ‖xi y-xi x.val‖ < eps x := by
    simpa only [mem_ball,dist_eq_norm] using hyx.2.2
  have hLower := (hControl x (B y) hyx.2.1 (xi y) hNear).2.1 v
  exact (mul_le_mul_of_nonneg_right (hkappaLe ⟨x,hxs⟩) (norm_nonneg v)).trans hLower

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.compact_native_restriction_reserve
