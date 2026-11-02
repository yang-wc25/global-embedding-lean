import Repair.EndpointActualJacobian
import Smoothing.ParameterGeometryModel

/-! The Jacobian in every actual receiving chart has a named finite-prefix
bound obtained only from the original transition derivative profiles. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def repairTransitionJacobianProfile (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * (∑ k ∈ Finset.range (j+1), T (k+1)) *
    bufferedTransitionPrefix T j ^ j

theorem repairTransitionJacobianProfile_nonneg
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (j : ℕ) :
    0 ≤ repairTransitionJacobianProfile T j := by
  unfold repairTransitionJacobianProfile
  exact mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun k _ => hT (k+1))))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hT j)) j)

theorem repairTransitionJacobianProfile_prefix
    (T U : ℕ → ℝ) (j : ℕ) (h : ∀ k ≤ j+1, T k = U k) :
    repairTransitionJacobianProfile T j = repairTransitionJacobianProfile U j := by
  unfold repairTransitionJacobianProfile bufferedTransitionPrefix
  have hsum : (∑ k ∈ Finset.range (j+1), T (k+1)) =
      ∑ k ∈ Finset.range (j+1), U (k+1) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h (k+1) (by have := Finset.mem_range.mp hk; omega)
  have hsum0 : (∑ k ∈ Finset.range (j+1), T k) =
      ∑ k ∈ Finset.range (j+1), U k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact h k (by have := Finset.mem_range.mp hk; omega)
  rw [hsum, hsum0]

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IT" => 𝓘(ℝ,D)

theorem repair_actual_observer_jacobian_jet
    (owner observer : OpenPartialHomeomorph M D)
    (howner : owner ∈ IsManifold.maximalAtlas IT ∞ M)
    (hobserver : observer ∈ IsManifold.maximalAtlas IT ∞ M)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (j : ℕ) (y : D) (hy : y ∈ (observer.symm.trans owner).source)
    (hForward : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (owner ∘ observer.symm) y‖ ≤ T k)
    (hInverse : ∀ k ≤ j+1,
      ‖iteratedFDeriv ℝ k (observer ∘ owner.symm) (owner (observer.symm y))‖ ≤ T k) :
    ‖iteratedFDeriv ℝ j (repairActualObserverJacobian owner observer) y‖ ≤
      repairTransitionJacobianProfile T j := by
  have hf := contDiffOn_actualChartTransition observer owner hobserver howner
  have hg := contDiffOn_actualChartTransition owner observer howner hobserver
  have hd := hg.fderiv_of_isOpen (owner.symm.trans observer).open_source (m := ∞) (by simp)
  have hMap : MapsTo (owner ∘ observer.symm) (observer.symm.trans owner).source
      (owner.symm.trans observer).source := by
    intro z hz
    refine ⟨owner.map_source hz.2, ?_⟩
    have hzo : observer.symm z ∈ owner.source := hz.2
    change owner.symm (owner (observer.symm z)) ∈ observer.source
    rw [owner.left_inv hzo]
    exact observer.map_target hz.1
  apply parameter_general_composition_jet_le T hT
    (observer.symm.trans owner).open_source (owner.symm.trans observer).open_source
    hf hd hMap hy j (∑ k ∈ Finset.range (j+1), T (k+1)) ?_ hForward
  intro k hk
  rw [norm_iteratedFDeriv_fderiv]
  exact (hInverse (k+1) (by omega)).trans
    (Finset.single_le_sum (fun a _ => hT (a+1)) (by simpa using hk))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairTransitionJacobianProfile_prefix
#print axioms GlobalEmbedding.Continuation.repair_actual_observer_jacobian_jet

