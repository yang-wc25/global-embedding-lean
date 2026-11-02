import Probes.Round3ParameterNativeFamily
import Probes.ActualSecondaryOriginalRemainderCoordinates

/-! The original native tensor coordinates of the same global mean-removed
metric error equal the actual native remainder in each parameter chart.
The totalized source differential identity is retained; no global smoothness
of an arbitrary outside extension is added as a hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {P M : Type*} [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary SubSecondary : Type*} [Fintype Label] [DecidableEq Label]
  [Fintype SubPrimary] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Label) (Β := SubPrimary) F)
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (length : ℕ) (tau delta : ℝ)
  (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
  (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
include hg hc

theorem round3Parameter_native_metric_with_mean_eq
    (B : OpenPartialHomeomorph P Ep) (t : Ep) (ht : t ∈ B.target) (x : M) :
    incrementsOriginalMetricError (fun z : Ep × M => F (B.symm z.1) z.2)
      (actualOriginalIncrementMap (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterNativePrimary F g B) (fun t => input (B.symm t)) length tau delta
        (round3ParameterNativeChoices choice B))
      (incrementsGlobalPrimaryMean (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterNativePrimary F g B) (fun t => input (B.symm t)) length tau) delta t x =
    incrementsOriginalMetricError (fun z : P × M => F z.1 z.2)
      (round3ParameterIncrementMap F hF g input length tau delta choice)
      (round3ParameterPrimaryMean F hF g input length tau) delta (B.symm t) x := by
  have hU := funext (round3Parameter_native_increment_eq F hF g B hg input length tau delta choice hc t ht)
  have hm : incrementsGlobalPrimaryMean (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterNativePrimary F g B) (fun t => input (B.symm t)) length tau t x =
      round3ParameterPrimaryMean F hF g input length tau (B.symm t) x :=
    round3ParameterPrimary_pullback_mean F hF g B hg input length tau t ht x
  unfold incrementsOriginalMetricError
  simp_rw [congrFun hU]
  rw [hm]

theorem round3Parameter_original_mean_removed_native
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (i : Fin A.count × Fin c) (z : Ep × D)
    (hz : z ∈ (B i.2).target ×ˢ (A.chart i.1).target) :
    actualOriginalNativeTargetTensor A B
      (incrementsOriginalMetricError (fun y : P × M => F y.1 y.2)
        (round3ParameterIncrementMap F hF g input length tau delta choice)
        (round3ParameterPrimaryMean F hF g input length tau) delta) i z =
    actualOriginalMeanRemovedMetric (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) (fun t => input ((B i.2).symm t)) length tau delta
      (round3ParameterNativeChoices choice (B i.2)) (A.chart i.1) z := by
  let Bid : Fin 1 → OpenPartialHomeomorph Ep Ep := fun _ => OpenPartialHomeomorph.refl Ep
  let FQ := fun t => F ((B i.2).symm t)
  let hFQ := fun t => hF ((B i.2).symm t)
  let gQ := round3ParameterNativePrimary F g (B i.2)
  let IQ := fun t => input ((B i.2).symm t)
  let cQ := round3ParameterNativeChoices choice (B i.2)
  let RQ := incrementsOriginalMetricError (fun y : Ep × M => FQ y.1 y.2)
    (actualOriginalIncrementMap FQ hFQ gQ IQ length tau delta cQ)
    (incrementsGlobalPrimaryMean FQ hFQ gQ IQ length tau) delta
  have he : actualOriginalNativeTargetTensor A B
      (incrementsOriginalMetricError (fun y : P × M => F y.1 y.2)
        (round3ParameterIncrementMap F hF g input length tau delta choice)
        (round3ParameterPrimaryMean F hF g input length tau) delta) i z =
      actualOriginalNativeTargetTensor A Bid RQ (i.1,0) z := by
    apply actual_bilinear_tensor_eq_of_basis
    intro a b
    simp only [actualOriginalNativeTargetTensor_basis]
    change _ = RQ z.1 ((A.chart i.1).symm z.2) _ _
    rw [show RQ z.1 ((A.chart i.1).symm z.2) = _ from
      round3Parameter_native_metric_with_mean_eq F hF g hg input length tau delta choice hc
        (B i.2) z.1 hz.1 ((A.chart i.1).symm z.2)]
  rw [he]
  have hn := actual_original_mean_removed_native_pullback A Bid hA FQ hFQ gQ IQ length tau delta cQ
    (i.1,0) (x := z) ⟨Set.mem_univ _,hz.2⟩
  simpa only [Bid, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
    parameterRound2_meanParameterMap, Function.comp_apply, id_eq] using hn

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_mean_removed_native
