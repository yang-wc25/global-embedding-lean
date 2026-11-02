import Probes.ActualHostRefinementCutoff
import Probes.ActualJointChartTransfer

/-! The actual produced host cutoff in its actual adapted coordinates.
The original host-cutoff jets, produced bump jets and actual inverse-chart
jets produce the full joint bound of that SAME supported scalar. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
variable {M : Type*} [TopologicalSpace M]

theorem actual_host_refinement_cutoff_adapted_jets
    (q : OpenPartialHomeomorph (Ep × M) X) (theta : Ep × M → ℝ) (eta : X → ℝ)
    (b : OpenPartialHomeomorph X X) (O : Set X) (hO : IsOpen O)
    (hOq : O ⊆ q.target) (hbo : b.source ⊆ O)
    (htheta : ContDiffOn ℝ ∞ (theta ∘ q.symm) O) (heta : ContDiff ℝ ∞ eta)
    (hbi : ContDiffOn ℝ ∞ b.symm b.target)
    (j : ℕ) (weight Mt Me : ℝ) (hweight : 0 < weight) (hMt : 0 ≤ Mt) (hMe : 0 ≤ Me)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (hthetaj : ∀ i ≤ j, ∀ x ∈ O, weight^i*‖iteratedFDeriv ℝ i (theta ∘ q.symm) x‖ ≤ Mt)
    (hetaj : ∀ i ≤ j, ∀ x, weight^i*‖iteratedFDeriv ℝ i eta x‖ ≤ Me)
    (hbij : ∀ i, 1 ≤ i → i ≤ j → ∀ y ∈ b.target,
      weight^(i-1)*‖iteratedFDeriv ℝ i b.symm y‖ ≤ T i)
    (y : X) (hy : y ∈ b.target) :
    weight^j*‖iteratedFDeriv ℝ j
      ((actualHostRefinementCutoff q theta eta) ∘ (q.trans b).symm) y‖ ≤
      actualFastChartTransferCost T j * (2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*Mt)*Me) := by
  classical
  let f : X → ℝ := fun x => theta (q.symm x)*eta x
  have hf : ContDiffOn ℝ ∞ f O := htheta.mul heta.contDiffOn
  have hmap : MapsTo b.symm b.target O := fun _ hx => hbo (b.map_target hx)
  have hfjet (i : ℕ) (hij : i ≤ j) :
      weight^i*‖iteratedFDeriv ℝ i f (b.symm y)‖ ≤ 2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*Mt)*Me := by
    have hb := slow_bilinear_jet_bound_norm (ContinuousLinearMap.mul ℝ ℝ)
      O hO (theta ∘ q.symm) eta htheta heta.contDiffOn i weight Mt Me hweight.le
      (b.symm y) (hmap hy) (fun k hk => hthetaj k (hk.trans hij) _ (hmap hy))
      (fun k hk => hetaj k (hk.trans hij) _)
    apply hb.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij)
        (mul_nonneg (ContinuousLinearMap.mul ℝ ℝ).opNorm_nonneg hMt)) hMe
  have hj := actual_fast_joint_chart_transfer T hT j b.symm f b.target O
    b.open_target hO hbi hf hmap y hy weight weight
    (2^j*(‖ContinuousLinearMap.mul ℝ ℝ‖*Mt)*Me) hweight le_rfl hfjet
    (fun i hi hij => hbij i hi hij y hy)
  have he : ((actualHostRefinementCutoff q theta eta) ∘ (q.trans b).symm) =ᶠ[𝓝 y] f ∘ b.symm := by
    filter_upwards [b.open_target.mem_nhds hy] with z hz
    have hqz := hOq (hbo (b.map_target hz))
    change (if q.symm (b.symm z) ∈ q.source then
      theta (q.symm (b.symm z))*eta (q (q.symm (b.symm z))) else 0) =
        theta (q.symm (b.symm z))*eta (b.symm z)
    rw [ite_eq_left (q.map_target hqz),q.right_inv hqz]
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact hj

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_host_refinement_cutoff_adapted_jets
