import Probes.Round3ParameterSecondaryGlobalNaturality

/-! # One actual global increment in all parameter charts

The complete literal primary-plus-secondary map precedes every observation
chart and derivative order.  Its native representative in each actual
parameter chart is proved equal to that same map, and the spatial metric
error agrees as a genuine tensor, without any new gluing of solver outputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary SubSecondary : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Label) (Β := SubPrimary) F)
  (B : OpenPartialHomeomorph P Q)
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (length : ℕ) (tau delta : ℝ)
  (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
  (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
include hg hc

theorem round3ParameterSecondary_pullback_sum (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterSecondarySum (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau delta
      (fun r a => (choice r a).pullback B) (t,x) =
      round3ParameterSecondarySum F hF g input length tau delta choice (B.symm t,x) := by
  unfold round3ParameterSecondarySum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  split_ifs with h
  · exact round3ParameterSecondary_pullback_piece F hF g B hg input length tau delta
      ((ν,μ),q) (choice ⟨((ν,μ),q),h⟩ a) (hc _ _) t ht x
  · rfl

theorem round3ParameterIncrement_pullback (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterIncrementMap (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau delta
      (fun r a => (choice r a).pullback B) (t,x) =
      round3ParameterIncrementMap F hF g input length tau delta choice (B.symm t,x) := by
  unfold round3ParameterIncrementMap
  rw [round3ParameterPrimary_pullback_wave F hF g B hg input length tau t ht,
    round3ParameterSecondary_pullback_sum F hF g B hg input length tau delta choice hc t ht]

theorem round3ParameterIncrement_pullback_metricError
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (t : Q) (ht : t ∈ B.target) (x : M) :
    incrementsOriginalMetricError (fun z : Q × M => F (B.symm z.1) z.2)
      (round3ParameterIncrementMap (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau delta
        (fun r a => (choice r a).pullback B))
      (fun t => H (B.symm t)) delta t x =
    incrementsOriginalMetricError (fun z : P × M => F z.1 z.2)
      (round3ParameterIncrementMap F hF g input length tau delta choice) H delta (B.symm t) x := by
  have hU := funext (round3ParameterIncrement_pullback F hF g B hg input length tau delta choice hc t ht)
  unfold incrementsOriginalMetricError
  simp_rw [congrFun hU]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterIncrement_pullback
#print axioms GlobalEmbedding.Continuation.round3ParameterIncrement_pullback_metricError
