import NormalPolar.PassiveRawObserverArgument
import Probes.ActualPositiveChartComposition

/-! Genuine changes of observer for physical fields and primary coordinate
maps. The compact transition cost is selected before the field, raw profile,
derivative order or reconstruction scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d : ℕ} {M Y : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem passiveRawObserverTransition_point
    (e host : OpenPartialHomeomorph M D) (z : X)
    (hz : z ∈ passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host) :
    ((passiveRawObserverTransition e host z).1,
      e.symm (passiveRawObserverTransition e host z).2) = (z.1,host.symm z.2) :=
  Prod.ext rfl (e.left_inv hz.2.2)

theorem passiveRaw_observer_field_transfer
    (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R)
    (hRO : R ⊆ passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
      ∀ (field : Ep × M → Y) (O S : Set X), IsOpen O → S ⊆ O →
        ContDiffOn ℝ ∞ (fun w : X => field (w.1,e.symm w.2)) O →
        ∀ (j : ℕ) (ell K : ℝ), 0 < ell → ell ≤ 1 → 0 ≤ K →
        (∀ k ≤ j, ∀ w ∈ S, ell^k*‖iteratedFDeriv ℝ k
          (fun w : X => field (w.1,e.symm w.2)) w‖ ≤ K) →
        ∀ k ≤ j, ∀ z ∈ R, passiveRawObserverTransition e host z ∈ S →
          ell^k*‖iteratedFDeriv ℝ k (fun w : X => field (w.1,host.symm w.2)) z‖ ≤
            actualFastChartTransferPrefix T j*K := by
  let phi := passiveRawObserverTransition (d := d) e host
  let V := passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host
  have hV : IsOpen V := passiveOriginalObserverDomain_open _ _ _
  have hphi : ContDiffOn ℝ ∞ phi V := passiveRawObserverTransition_smooth e host he hh
  obtain ⟨T,hT,hTb⟩ := round3_prepared_compact_profiles phi V R hV hR hRO hphi
  refine ⟨T,hT,?_⟩
  intro field O S hO hSO hf j ell K hell hell1 hK hb k hk z hz hzS
  let U := V ∩ phi ⁻¹' O
  have hU : IsOpen U := hphi.continuousOn.isOpen_inter_preimage hV hO
  have hzU : z ∈ U := ⟨hRO hz,hSO hzS⟩
  let f := fun w : X => field (w.1,e.symm w.2)
  have h := actual_fast_joint_chart_transfer T hT k phi f U O hU hO
    (hphi.mono inter_subset_left) hf (fun w hw => hw.2) z hzU ell ell K hell le_rfl
    (fun a ha => hb a (ha.trans hk) (phi z) hzS)
    (fun a _ _ => (hTb ell hell.le hell1 a z hz).2)
  have heq : EqOn (fun w : X => field (w.1,host.symm w.2)) (f ∘ phi) U := by
    intro w hw
    change field (w.1,host.symm w.2) = field ((phi w).1,e.symm (phi w).2)
    rw [passiveRawObserverTransition_point e host w hw.1]
  have hnear := heq.eventuallyEq_of_mem (hU.mem_nhds hzU)
  rw [(hnear.iteratedFDeriv ℝ k).eq_of_nhds]
  exact h.trans (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hk) hK)

theorem passiveRaw_observer_positive_field_transfer
    (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R)
    (hRO : R ⊆ passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
      ∀ (field : Ep × M → Y) (O S : Set X), IsOpen O → S ⊆ O →
        ContDiffOn ℝ ∞ (fun w : X => field (w.1,e.symm w.2)) O →
        ∀ (j : ℕ) (ell K : ℝ), 0 < ell → ell ≤ 1 → 0 ≤ K →
        (∀ k, 1 ≤ k → k ≤ j → ∀ w ∈ S, ell^(k-1)*‖iteratedFDeriv ℝ k
          (fun w : X => field (w.1,e.symm w.2)) w‖ ≤ K) →
        ∀ k, 1 ≤ k → k ≤ j → ∀ z ∈ R, passiveRawObserverTransition e host z ∈ S →
          ell^(k-1)*‖iteratedFDeriv ℝ k (fun w : X => field (w.1,host.symm w.2)) z‖ ≤
            actualFastChartTransferPrefix T j*K := by
  let phi := passiveRawObserverTransition (d := d) e host
  let V := passiveOriginalObserverDomain (OpenPartialHomeomorph.refl Ep) e host
  have hV : IsOpen V := passiveOriginalObserverDomain_open _ _ _
  have hphi : ContDiffOn ℝ ∞ phi V := passiveRawObserverTransition_smooth e host he hh
  obtain ⟨T,hT,hTb⟩ := round3_prepared_compact_profiles phi V R hV hR hRO hphi
  refine ⟨T,hT,?_⟩
  intro field O S hO hSO hf j ell K hell hell1 hK hb k hk1 hk z hz hzS
  let U := V ∩ phi ⁻¹' O
  have hU : IsOpen U := hphi.continuousOn.isOpen_inter_preimage hV hO
  have hzU : z ∈ U := ⟨hRO hz,hSO hzS⟩
  let f := fun w : X => field (w.1,e.symm w.2)
  have h := actual_positive_joint_chart_composition T hT k hk1 phi f U O hU hO
    (hphi.mono inter_subset_left) hf (fun w hw => hw.2) z hzU ell K hell hK
    (fun a ha hka => hb a ha (hka.trans hk) (phi z) hzS)
    (fun a _ _ => (hTb ell hell.le hell1 a z hz).2)
  have heq : EqOn (fun w : X => field (w.1,host.symm w.2)) (f ∘ phi) U := by
    intro w hw
    change field (w.1,host.symm w.2) = field ((phi w).1,e.symm (phi w).2)
    rw [passiveRawObserverTransition_point e host w hw.1]
  have hnear := heq.eventuallyEq_of_mem (hU.mem_nhds hzU)
  rw [(hnear.iteratedFDeriv ℝ k).eq_of_nhds]
  exact h.trans (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hk) hK)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRaw_observer_field_transfer
#print axioms GlobalEmbedding.Continuation.passiveRaw_observer_positive_field_transfer
