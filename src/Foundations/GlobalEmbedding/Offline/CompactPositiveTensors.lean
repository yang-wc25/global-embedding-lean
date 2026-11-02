import GlobalEmbedding.Offline.ContinuousRankOneBasis
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Compact classes of actual positive symmetric source tensors

The tensor is the native continuous bilinear form on the fixed source model.
Symmetry and the displayed coercivity inequality are closed conditions; the
actual operator-norm upper bound makes their intersection compact in finite
dimension.  No compactness of an unspecified positive cone is assumed.
-/

namespace GlobalEmbedding.Offline

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def boundedPositiveTensorSet (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (lam R : ℝ) : Set (V →L[ℝ] V →L[ℝ] ℝ) :=
  {g | (∀ x y, g x y = g y x) ∧ (∀ v, lam * ‖v‖ ^ 2 ≤ g v v) ∧ ‖g‖ ≤ R}

theorem boundedPositiveTensorSet_isClosed (lam R : ℝ) :
    IsClosed (boundedPositiveTensorSet V lam R) := by
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  have heval (x y : V) : Continuous (fun g : V →L[ℝ] V →L[ℝ] ℝ ↦ g x y) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  have hs : IsClosed {g : V →L[ℝ] V →L[ℝ] ℝ | ∀ x y, g x y = g y x} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq (heval x y) (heval y x)
  have hl : IsClosed {g : V →L[ℝ] V →L[ℝ] ℝ | ∀ v, lam * ‖v‖ ^ 2 ≤ g v v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v ↦ isClosed_le continuous_const (heval v v)
  have hn : IsClosed {g : V →L[ℝ] V →L[ℝ] ℝ | ‖g‖ ≤ R} :=
    isClosed_le continuous_norm continuous_const
  exact hs.inter (hl.inter hn)

theorem boundedPositiveTensorSet_isCompact [FiniteDimensional ℝ V] (lam R : ℝ) :
    IsCompact (boundedPositiveTensorSet V lam R) := by
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  apply (isCompact_closedBall (0 : V →L[ℝ] V →L[ℝ] ℝ) R).of_isClosed_subset
    (boundedPositiveTensorSet_isClosed lam R)
  intro g hg
  simpa only [Metric.mem_closedBall, dist_zero_right] using hg.2.2

theorem boundedPositiveTensorSet_posDef {lam R : ℝ} (hlam : 0 < lam)
    {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : g ∈ boundedPositiveTensorSet V lam R) :
    ∀ v, v ≠ 0 → 0 < g v v := by
  intro v hv
  exact (mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hg.2.1 v)

#print axioms boundedPositiveTensorSet_isCompact
#print axioms boundedPositiveTensorSet_posDef

end GlobalEmbedding.Offline
