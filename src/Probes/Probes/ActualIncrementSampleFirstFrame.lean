import Probes.ActualFirstFrameChartTransfer

/-! Actual first frames and shifted ordinary Hessians on original sampling
sets, using their real open differentiation domains. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
variable {M : Type*} [TopologicalSpace M]

theorem actual_first_frame_hessian_transferred_on_samples
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (F : Ep → M → V) (e0 e1 : Ep → OpenPartialHomeomorph M D)
    (U W S S0 : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hSU : S ⊆ U) (hS0W : S0 ⊆ W)
    (hF0 : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e0 z.1).symm z.2)) W)
    (hphi : ContDiffOn ℝ ∞ (actualSourceChartTransition e0 e1) U)
    (hmap : MapsTo (actualSourceChartTransition e0 e1) U W)
    (hsample : MapsTo (actualSourceChartTransition e0 e1) S S0)
    (hcoord : ∀ z ∈ U, (e1 z.1).symm z.2 ∈ (e0 z.1).source)
    (ell K : ℝ) (hell : 0 < ell) (hK : 0 ≤ K)
    (hAj : ∀ k ≤ j+1, ∀ z ∈ S0, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e0 y.1).symm) y.2) z‖ ≤ K)
    (hphijet : ∀ k, 1 ≤ k → k ≤ j+2 → ∀ z ∈ S,
      ell^(k-1)*‖iteratedFDeriv ℝ k (actualSourceChartTransition e0 e1) z‖ ≤ T k) :
    ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e1 z.1).symm z.2)) U ∧
    ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e1 z.1).symm) z.2) U ∧
    ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e1 z.1).symm)) z.2) U ∧
    ∀ k ≤ j, ∀ z ∈ S,
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
  have hbound (k : ℕ) (hk : k ≤ j+1) (z : X) (hz : z ∈ S) :
      ell^k * ‖iteratedFDeriv ℝ k A1 z‖ ≤ actualFirstFrameTransferCost T (j+1)*K := by
    have heq : A1 =ᶠ[𝓝 z] R := Filter.eventuallyEq_of_mem (hU.mem_nhds (hSU hz)) (fun y hy =>
      actual_first_frame_true_chart_transition F e0 e1 U W hU hW hF0 hphi hmap hcoord y hy)
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (actual_first_frame_pullback_jets T hT (j+1) phi A0 U W hU hW hphi hA0 hmap z (hSU hz)
      ell K hell hK (fun i hi => hAj i hi (phi z) (hsample hz))
      (fun i hi hij => hphijet i hi (by omega) z hz)).2 k hk
  intro k hk z hz
  refine ⟨hbound k (by omega) z hz,?_⟩
  exact (mul_le_mul_of_nonneg_left (spatial_first_jet_le hU hA1 (hSU hz) k)
    (pow_nonneg hell.le (k+1))).trans (hbound (k+1) (by omega) z hz)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_first_frame_hessian_transferred_on_samples
