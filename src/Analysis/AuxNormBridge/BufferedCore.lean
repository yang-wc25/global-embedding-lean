import Repair.ReferenceAuxiliaryGeometry

/-!
# A compact protected core from the unchanged original buffered atlas

The original inner coordinate image has a bounded radius and its original
buffer keeps its closure inside the same chart target.  This constructs the
compact set used for the auxiliary-norm comparison; no compactness of the
original norm domain is required, and that norm domain is not replaced.

The positive comparison constant is fixed before any reference map.  It is
a maximum of fixed geometric bounds, without a chart-count multiplier.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold IsManifold Set Function Metric Bundle
open scoped ContDiff Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GlobalEmbedding.Continuation.AuxNormBridge

section MetricCore
variable {E M : Type*} [MetricSpace E] [TopologicalSpace M]

/-- The actual closed inner coordinate image.  It is an auxiliary compact
set for a proof, never a replacement for the input norm domain. -/
def protectedInnerClosure (A : BufferedAtlas M E) (i : Fin A.count) : Set E :=
  closure ((A.chart i) '' A.inner i)

/-- The original buffer itself puts the constructed closed inner image in
the original chart target; no added collar hypothesis occurs. -/
theorem protectedInnerClosure_subset_target (A : BufferedAtlas M E)
    (i : Fin A.count) : protectedInnerClosure A i ⊆ (A.chart i).target := by
  intro y hy
  obtain ⟨u, hu, hyu⟩ := Metric.mem_closure_iff.mp hy A.buffer A.buffer_pos
  obtain ⟨x, hx, rfl⟩ := hu
  exact A.buffered i x hx (mem_ball.mpr hyu)

/-- Original coordinate-radius control makes the constructed core compact.
The domain and the coordinate map remain literally the original ones. -/
theorem protectedInnerClosure_isCompact [ProperSpace E] (A : BufferedAtlas M E)
    (centers : Fin A.count → E) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius)
    (i : Fin A.count) : IsCompact (protectedInnerClosure A i) := by
  exact (isCompact_closedBall (centers i) radius).of_isClosed_subset
    isClosed_closure (closure_minimal (hBound i) isClosed_closedBall)

/-- Every original inner point is sampled by the constructed core. -/
theorem mem_protectedInnerClosure (A : BufferedAtlas M E)
    (i : Fin A.count) (x : M) (hx : x ∈ A.inner i) :
    A.chart i x ∈ protectedInnerClosure A i :=
  subset_closure ⟨x, hx, rfl⟩

/-- The core is a compact subset of the same physical source chart. -/
theorem protectedInnerCarrier_isCompact [ProperSpace E] (A : BufferedAtlas M E)
    (centers : Fin A.count → E) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius)
    (i : Fin A.count) :
    IsCompact ((A.chart i).symm '' protectedInnerClosure A i) :=
  (protectedInnerClosure_isCompact A centers radius hBound i).image_of_continuousOn
    ((A.chart i).symm.continuousOn.mono (protectedInnerClosure_subset_target A i))

end MetricCore

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
local notation "D" => EuclideanSpace ℝ (Fin n)

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _)]
local notation "I" => 𝓘(ℝ,D)

/-- The fixed original auxiliary norm supplies one chart bound on every
original inner domain.  Its compact samples are manufactured from the
original buffer and radius, before the map, metric, or parameters are read.
No compactness assumption is made on any original norm domain. -/
theorem original_inner_auxiliary_bound_exists
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (centers : Fin A.count → D) (radius : ℝ)
    (hBound : ∀ i, (A.chart i) '' A.inner i ⊆ closedBall (centers i) radius) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x, x ∈ A.inner i →
      ‖mfderiv I I (A.chart i) x‖ ≤ C := by
  classical
  have hEach : ∀ i : Fin A.count, ∃ R : ℝ, 0 < R ∧
      ∀ y ∈ protectedInnerClosure A i,
        ‖mfderiv I I (A.chart i) ((A.chart i).symm y)‖ ≤ R := by
    intro i
    exact repair_auxiliary_chart_bound (A.chart i) (hA.chart_mem i)
      (protectedInnerClosure A i)
      (protectedInnerClosure_isCompact A centers radius hBound i)
      (protectedInnerClosure_subset_target A i)
  choose R hR hBounds using hEach
  obtain ⟨B, hB⟩ := (Set.finite_range R).bddAbove
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro i x hx
  have hi := hBounds i (A.chart i x) (mem_protectedInnerClosure A i x hx)
  rw [(A.chart i).left_inv (A.inner_subset i hx)] at hi
  exact hi.trans ((hB (mem_range_self i)).trans (le_max_right _ _))

end GlobalEmbedding.Continuation.AuxNormBridge

#print axioms GlobalEmbedding.Continuation.AuxNormBridge.protectedInnerClosure_subset_target
#print axioms GlobalEmbedding.Continuation.AuxNormBridge.protectedInnerClosure_isCompact
#print axioms GlobalEmbedding.Continuation.AuxNormBridge.original_inner_auxiliary_bound_exists
