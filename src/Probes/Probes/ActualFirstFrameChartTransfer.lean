import Probes.ActualNormalHessianTransfer

/-!
# Actual first frames and the necessary ordinary Hessian shift

The true first frame is transported by one actual spatial Jacobian. Its
positive slow jets remain of shift zero. Differentiating that same first
frame gives the ordinary adapted Hessian with shift one. This deliberately
keeps the distinction from the normal Hessian, whose shift is zero.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def actualFirstFrameTransferCost (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  2^j * actualFastChartTransferPrefix T j * bufferedTransitionPrefix T (j+1)

theorem actualFirstFrameTransferCost_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) :
    0 ≤ actualFirstFrameTransferCost T j :=
  mul_nonneg (mul_nonneg (by positivity) (actualFastChartTransferPrefix_nonneg T hT j))
    (zero_le_one.trans (one_le_bufferedTransitionPrefix hT (j+1)))

section Transfer
variable {Ep Es Eq Et V : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem actual_first_frame_pullback_jets
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (phi : Ep × Es → Eq × Et) (A : Eq × Et → Et →L[ℝ] V)
    (U : Set (Ep × Es)) (W : Set (Eq × Et)) (hU : IsOpen U) (hW : IsOpen W)
    (hphi : ContDiffOn ℝ ∞ phi U) (hA : ContDiffOn ℝ ∞ A W)
    (hmap : MapsTo phi U W) (x : Ep × Es) (hx : x ∈ U)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K)
    (hAj : ∀ i ≤ j, ell^i * ‖iteratedFDeriv ℝ i A (phi x)‖ ≤ K)
    (hphijet : ∀ i, 1 ≤ i → i ≤ j+1 →
      ell^(i-1)*‖iteratedFDeriv ℝ i phi x‖ ≤ T i) :
    ContDiffOn ℝ ∞ (fun z => (A (phi z)).comp (actualJointSpatialJacobian phi z)) U ∧
      ∀ i ≤ j, ell^i * ‖iteratedFDeriv ℝ i
        (fun z => (A (phi z)).comp (actualJointSpatialJacobian phi z)) x‖ ≤
          actualFirstFrameTransferCost T j * K := by
  obtain ⟨hL,hLj⟩ := actual_joint_spatial_jacobian_fast_jets T hT j phi U hU hphi x hx
    ell ell hell le_rfl hphijet
  have hAc : ContDiffOn ℝ ∞ (A ∘ phi) U := hA.comp hphi hmap
  have hAcj : ∀ i ≤ j, ell^i * ‖iteratedFDeriv ℝ i (A ∘ phi) x‖ ≤
      actualFastChartTransferPrefix T j * K := by
    intro i hi
    have hb := actual_fast_joint_chart_transfer T hT i phi A U W hU hW hphi hA hmap x hx
      ell ell K hell le_rfl (fun k hk => hAj k (hk.trans hi))
      (fun k hk hki => hphijet k hk (by omega))
    exact hb.trans (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hi) hK)
  obtain ⟨hs,hb⟩ := actual_clm_comp_uniform_slow_jets (A ∘ phi)
    (actualJointSpatialJacobian phi) U hU hAc hL j ell
    (actualFastChartTransferPrefix T j*K) (bufferedTransitionPrefix T (j+1)) hell.le
    (mul_nonneg (actualFastChartTransferPrefix_nonneg T hT j) hK)
    (zero_le_one.trans (one_le_bufferedTransitionPrefix hT (j+1))) x hx hAcj hLj
  refine ⟨hs,fun i hi => (hb i hi).trans_eq ?_⟩
  unfold actualFirstFrameTransferCost
  ring
end Transfer

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
variable {M : Type*} [TopologicalSpace M]

theorem actual_first_frame_true_chart_transition
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (z : X) (hz : z ∈ U) :
    fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2 =
      (fderiv ℝ (F z.1 ∘ (e0 z.1).symm) (actualSourceChartTransition e0 e1 z).2).comp
        (actualJointSpatialJacobian (actualSourceChartTransition e0 e1) z) := by
  let f0 := F z.1 ∘ (e0 z.1).symm
  let f1 := F z.1 ∘ (e1 z.1).symm
  let t : D → D := fun x => e0 z.1 ((e1 z.1).symm x)
  have hf0 : DifferentiableAt ℝ f0 (t z.2) := by
    have hh := (hF0.contDiffAt (hW.mem_nhds (hmap hz))).comp (t z.2)
      (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by simp)
  have ht : DifferentiableAt ℝ t z.2 := by
    have hh := (hphi.snd.contDiffAt (hU.mem_nhds hz)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id)
    exact hh.differentiableAt (by simp)
  have heq : f1 =ᶠ[𝓝 z.2] f0 ∘ t := by
    filter_upwards [(hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz] with x hx
    change F z.1 ((e1 z.1).symm x) = F z.1 ((e0 z.1).symm (e0 z.1 ((e1 z.1).symm x)))
    rw [(e0 z.1).left_inv (hcoord (z.1,x) hx)]
  exact heq.fderiv_eq.trans (fderiv_comp z.2 hf0 ht)

/-- Original first-frame jets and the actual transition produce both adapted
geometric profiles. No adapted derivative bound is an input. -/
theorem actual_first_frame_hessian_transferred_from_original_jets
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hcoord : ∀ z ∈ U, (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K)
    (hAj : ∀ k ≤ j+1, ∀ z ∈ W, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e0 y.1).symm) y.2) z‖ ≤ K)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ U,
      ell^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition e0 e1) z‖ ≤ T k) :
    ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e1 z.1).symm z.2)) U ∧
    ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2) U ∧
    ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e1 z.1).symm)) z.2) U ∧
    ∀ k ≤ j, ∀ z ∈ U,
      ell^k * ‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (F y.1 ∘ (e1 y.1).symm) y.2) z‖ ≤
          actualFirstFrameTransferCost T (j+1)*K ∧
      ell^(k+1) * ‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e1 y.1).symm)) y.2) z‖ ≤
          actualFirstFrameTransferCost T (j+1)*K := by
  let A0 : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e0 z.1).symm) z.2
  let A1 : X → D →L[ℝ] V := fun z => fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2
  let phi := actualSourceChartTransition e0 e1
  let R : X → D →L[ℝ] V := fun z => (A0 (phi z)).comp (actualJointSpatialJacobian phi z)
  have hA0 : ContDiffOn ℝ ∞ A0 W :=
    (incrementsJointSpatialJets_bridge _ W hW hF0).2.1
  have hF1 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e1 z.1).symm z.2)) U := by
    apply (hF0.comp hphi hmap).congr
    intro z hz
    change F z.1 ((e1 z.1).symm z.2) = F z.1 ((e0 z.1).symm (e0 z.1 ((e1 z.1).symm z.2)))
    rw [(e0 z.1).left_inv (hcoord z hz)]
  have hA1 : ContDiffOn ℝ ∞ A1 U := (incrementsJointSpatialJets_bridge _ U hU hF1).2.1
  refine ⟨hF1,hA1,(incrementsJointSpatialJets_bridge _ U hU hF1).2.2,?_⟩
  have hbound (k : ℕ) (hk : k ≤ j+1) (z : X) (hz : z ∈ U) :
      ell^k * ‖iteratedFDeriv ℝ k A1 z‖ ≤ actualFirstFrameTransferCost T (j+1)*K := by
    have heq : A1 =ᶠ[𝓝 z] R := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy =>
      actual_first_frame_true_chart_transition F e0 e1 U W hU hW hF0 hphi hmap hcoord y hy)
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (actual_first_frame_pullback_jets T hT (j+1) phi A0 U W hU hW hphi hA0 hmap z hz
      ell K hell hK (fun i hi => hAj i hi (phi z) (hmap hz))
      (fun i hi hij => hphijet i hi (by omega) z hz)).2 k hk
  intro k hk z hz
  refine ⟨hbound k (by omega) z hz,?_⟩
  exact (mul_le_mul_of_nonneg_left (spatial_first_jet_le hU hA1 hz k)
    (pow_nonneg hell.le (k+1))).trans (hbound (k+1) (by omega) z hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_first_frame_pullback_jets
#print axioms GlobalEmbedding.Continuation.actual_first_frame_true_chart_transition
#print axioms GlobalEmbedding.Continuation.actual_first_frame_hessian_transferred_from_original_jets
