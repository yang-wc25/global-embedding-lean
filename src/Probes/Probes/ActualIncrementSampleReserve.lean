import Probes.ActualAdaptedFirstFrameReserve

/-! Original sampled coercivity and qualitative immersion are transported
separately through the same genuine chart inverse. -/
noncomputable section
open Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
variable {M : Type*} [TopologicalSpace M]

theorem actual_adapted_first_frame_injective
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e1 e0) W)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (hinj : ∀ z ∈ W, Function.Injective (fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2)) :
    ∀ z ∈ U, Function.Injective (fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2) := by
  intro z hz
  let phi := actualSourceChartTransition e0 e1
  let back := actualSourceChartTransition e1 e0
  have hSJ := actual_source_chart_spatial_jacobian_inverse e0 e1 U W hU hW
    hphi hback hmap hcoord z hz
  have hleft : Function.LeftInverse (actualJointSpatialJacobian back (phi z))
      (actualJointSpatialJacobian phi z) := by
    intro v
    exact congrArg (fun L : D →L[ℝ] D => L v) hSJ
  rw [actual_first_frame_true_chart_transition F e0 e1 U W hU hW hF0 hphi hmap
    (fun y hy => (hcoord y hy).2) z hz]
  exact (hinj (phi z) (hmap hz)).comp hleft.injective

theorem actual_adapted_first_frame_reserve_on_samples
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W S S0 : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hSU : S ⊆ U)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hback : ContDiffOn ℝ ∞ (actualSourceChartTransition e1 e0) W)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hsample : MapsTo (actualSourceChartTransition e0 e1) S S0)
    (hcoord : ∀ z ∈ U, z.2 ∈ (e1 z.1).target ∧ (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (c B : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hreserve : ∀ z ∈ S0, ∀ v : D,
      c*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2 v‖^2)
    (hbackBound : ∀ z ∈ S0, ‖fderiv ℝ (actualSourceChartTransition e1 e0) z‖ ≤ B) :
    ∀ z ∈ S, ∀ v : D,
      (c/B^2)*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2 v‖^2 := by
  intro z hz v
  have hzU := hSU hz
  let phi := actualSourceChartTransition e0 e1
  let back := actualSourceChartTransition e1 e0
  have hJn : ‖actualJointSpatialJacobian back (phi z)‖ ≤ B := by
    have hs := spatial_first_jet_le hW hback.snd (hmap hzU) 0
    simp only [norm_iteratedFDeriv_zero] at hs
    rw [norm_iteratedFDeriv_one] at hs
    have hp := (ContinuousLinearMap.snd ℝ Ep D).norm_iteratedFDeriv_comp_left
      (hback.contDiffAt (hW.mem_nhds (hmap hzU))) (n := 1) (by simp)
    rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one] at hp
    have hp1 := hp.trans (mul_le_of_le_one_left (norm_nonneg _)
      (ContinuousLinearMap.norm_snd_le ℝ Ep D))
    exact hs.trans (hp1.trans (hbackBound (phi z) (hsample hz)))
  rw [actual_first_frame_true_chart_transition F e0 e1 U W hU hW hF0 hphi hmap
    (fun y hy => (hcoord y hy).2) z hzU]
  exact actual_frame_reserve_of_left_inverse _ _ _
    (actual_source_chart_spatial_jacobian_inverse e0 e1 U W hU hW hphi hback hmap hcoord z hzU)
    c B hc.le hB hJn (hreserve (phi z) (hsample hz)) v

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_adapted_first_frame_injective
#print axioms GlobalEmbedding.Continuation.actual_adapted_first_frame_reserve_on_samples
