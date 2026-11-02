import Probes.ActualFirstFrameChartTransfer

/-!
# The adapted first-frame reserve is an output of the true chart inverse

The two actual spatial Jacobians on an original/adapted overlap are mutual
inverses. A forward coordinate derivative bound transports the original
first-frame coercivity to the adapted frame without assuming that reserve.
-/

noncomputable section
open Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

theorem actual_frame_reserve_of_left_inverse
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : E →L[ℝ] V) (J S : E →L[ℝ] E)
    (hSJ : S.comp J = ContinuousLinearMap.id ℝ E)
    (c B : ℝ) (hc : 0 ≤ c) (hB : 0 < B) (hS : ‖S‖ ≤ B)
    (hA : ∀ v, c*‖v‖^2 ≤ ‖A v‖^2) :
    ∀ v, (c/B^2)*‖v‖^2 ≤ ‖A (J v)‖^2 := by
  intro v
  have hv : S (J v) = v := congrArg (fun L : E →L[ℝ] E => L v) hSJ
  have hn : ‖v‖ ≤ B*‖J v‖ := by
    have hh := S.le_of_opNorm_le hS (J v)
    rwa [hv] at hh
  have hn2 : ‖v‖^2 ≤ B^2*‖J v‖^2 := by
    have hh := mul_le_mul hn hn (norm_nonneg _) (mul_nonneg hB.le (norm_nonneg _))
    nlinarith only [hh]
  have he : c/B^2*‖v‖^2 = (c*‖v‖^2)/B^2 := by ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hB)).2
  have hleft := mul_le_mul_of_nonneg_left hn2 hc
  have hright := mul_le_mul_of_nonneg_left (hA (J v)) (sq_nonneg B)
  nlinarith only [hleft,hright]

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
variable {M : Type*} [TopologicalSpace M]

theorem actual_source_chart_spatial_jacobian_inverse
    (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e1 e0) W)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (z : X) (hz : z ∈ U) :
    (actualJointSpatialJacobian (actualSourceChartTransition e1 e0)
      (actualSourceChartTransition e0 e1 z)).comp
        (actualJointSpatialJacobian (actualSourceChartTransition e0 e1) z) =
          ContinuousLinearMap.id ℝ D := by
  let t : D → D := fun x => e0 z.1 ((e1 z.1).symm x)
  let s : D → D := fun x => e1 z.1 ((e0 z.1).symm x)
  have ht : DifferentiableAt ℝ t z.2 := by
    have hh := (hphi.snd.contDiffAt (hU.mem_nhds hz)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by simp)
  have hs : DifferentiableAt ℝ s (t z.2) := by
    have hh := (hback.snd.contDiffAt (hW.mem_nhds (hmap hz))).comp (t z.2)
      (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by simp)
  have heq : s ∘ t =ᶠ[𝓝 z.2] id := by
    filter_upwards [(hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz] with x hx
    change e1 z.1 ((e0 z.1).symm (e0 z.1 ((e1 z.1).symm x))) = x
    rw [(e0 z.1).left_inv (hcoord (z.1,x) hx).2,(e1 z.1).right_inv (hcoord (z.1,x) hx).1]
  have hh := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp z.2 hs ht,fderiv_id] at hh
  exact hh

theorem actual_adapted_first_frame_reserve_from_original
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e1 e0) W)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (c B : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hreserve : ∀ z ∈ W, ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2 v‖^2)
    (hbackBound : ∀ z ∈ W, ‖fderiv ℝ (actualSourceChartTransition e1 e0) z‖ ≤ B) :
    ∀ z ∈ U, ∀ v : D,
      (c/B^2)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2 v‖^2 := by
  intro z hz v
  let phi := actualSourceChartTransition e0 e1
  let back := actualSourceChartTransition e1 e0
  have hJn : ‖actualJointSpatialJacobian back (phi z)‖ ≤ B := by
    have hs := spatial_first_jet_le hW hback.snd (hmap hz) 0
    simp only [norm_iteratedFDeriv_zero] at hs
    rw [norm_iteratedFDeriv_one] at hs
    have hp := (ContinuousLinearMap.snd ℝ Ep D).norm_iteratedFDeriv_comp_left
      (hback.contDiffAt (hW.mem_nhds (hmap hz))) (n := 1) (by simp)
    rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one] at hp
    have hp1 := hp.trans (mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.norm_snd_le ℝ Ep D))
    exact hs.trans (hp1.trans (hbackBound (phi z) (hmap hz)))
  rw [actual_first_frame_true_chart_transition F e0 e1 U W hU hW hF0 hphi hmap
    (fun y hy => (hcoord y hy).2) z hz]
  exact actual_frame_reserve_of_left_inverse _ _ _
    (actual_source_chart_spatial_jacobian_inverse e0 e1 U W hU hW hphi hback hmap hcoord z hz)
    c B hc.le hB hJn (hreserve (phi z) (hmap hz)) v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_source_chart_spatial_jacobian_inverse
#print axioms GlobalEmbedding.Continuation.actual_adapted_first_frame_reserve_from_original
