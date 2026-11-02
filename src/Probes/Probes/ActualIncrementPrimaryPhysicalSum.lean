import Probes.ActualIncrementPrimaryObservationSum
import Probes.ActualSecondaryConstructedCancellation
import Probes.ActualSecondaryObservedSupport

/-! Actual primary metric linearization commutes with the SAME supported
finite wave sum. Inactive physical tensors have true zero germs derived from
the displacement support. Only the actual active primary/subordinate counts
occur, and the external delta is retained exactly. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Eq P Label Sub : Type*}
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [TopologicalSpace P]
  [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Eq × D
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

private local instance primarySumTensorSemi : SeminormedAddCommGroup Tensor :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance primarySumTensorNormed : NormedAddCommGroup Tensor :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance primarySumTensorSpace : NormedSpace ℝ Tensor :=
  ContinuousLinearMap.toNormedSpace

theorem actual_primary_physical_sum_weighted_jets
    (Fobs : X → V) (waves : Label → Sub → P → V)
    (K : Label → Set P) (Ksub : Label → Sub → Set P)
    (hsub : ∀ ν β, Ksub ν β ⊆ K ν)
    (W : Set P) (hW : IsOpen W)
    (hsupport : ∀ ν β, tsupport (fun y : W => waves ν β y) ⊆ Subtype.val ⁻¹' Ksub ν β)
    (kappa : X → P) (Omega S : Set X) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : Label → Sub → Set X) (hO : ∀ ν β, IsOpen (O ν β))
    (hactiveO : ∀ ν β, Omega ∩ kappa ⁻¹' Ksub ν β ⊆ O ν β)
    (hreg : ∀ ν β, ContDiffOn ℝ ∞ (waves ν β ∘ kappa) (O ν β))
    (hEreg : ∀ ν β, ContDiffOn ℝ ∞
      (actualJointMetricLinearization Fobs (waves ν β ∘ kappa)) (O ν β))
    (L R j : ℕ)
    (hL : ∀ x ∈ S, (Finset.univ.filter (fun ν => kappa x ∈ K ν)).card ≤ L)
    (hR : ∀ ν, ∀ x ∈ S, (Finset.univ.filter (fun β => kappa x ∈ Ksub ν β)).card ≤ R)
    (tau Budget : ℝ) (htau : 0 < tau) (hBudget : 0 ≤ Budget)
    (hbound : ∀ ν β, ∀ r ≤ j, ∀ x ∈ S ∩ kappa ⁻¹' Ksub ν β,
      tau^r * ‖iteratedFDeriv ℝ r
        (actualJointMetricLinearization Fobs (waves ν β ∘ kappa)) x‖ ≤ Budget) :
    let U := fun y => ∑ ν, ∑ β, waves ν β (kappa y)
    ContDiffOn ℝ ∞ U Omega ∧ ContDiffOn ℝ ∞ (actualJointMetricLinearization Fobs U) Omega ∧
      ∀ delta : ℝ, ∀ r ≤ j, ∀ x ∈ S,
      tau^r * ‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs (fun y => delta • U y)) x‖ ≤
        ((L*R:ℕ):ℝ)*Budget*|delta| := by
  intro U
  let E := fun ν β => actualJointMetricLinearization Fobs (waves ν β ∘ kappa)
  have hzero (ν : Label) (β : Sub) (x : X) (hx : x ∈ Omega) (hn : kappa x ∉ Ksub ν β) :
      waves ν β ∘ kappa =ᶠ[𝓝 x] fun _ => 0 :=
    parameterRound2_relative_observation_zero_germ (waves ν β) W (Ksub ν β) hW (hsupport ν β)
      kappa x (hkappa.continuousAt (hOmega.mem_nhds hx)) (hmap hx) hn
  have hEzero (ν : Label) (β : Sub) (x : X) (hx : x ∈ Omega) (hn : kappa x ∉ Ksub ν β) :
      E ν β =ᶠ[𝓝 x] fun _ => 0 :=
    actual_joint_metric_linearization_zero_germ Fobs (waves ν β ∘ kappa) x (hzero ν β x hx hn)
  have hfull (ν : Label) (β : Sub) : ContDiffOn ℝ ∞ (waves ν β ∘ kappa) Omega := by
    intro x hx
    by_cases hm : kappa x ∈ Ksub ν β
    · exact ((hreg ν β).contDiffAt ((hO ν β).mem_nhds (hactiveO ν β ⟨hx,hm⟩))).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hzero ν β x hx hm)).contDiffWithinAt
  have hEfull (ν : Label) (β : Sub) : ContDiffOn ℝ ∞ (E ν β) Omega := by
    intro x hx
    by_cases hm : kappa x ∈ Ksub ν β
    · exact ((hEreg ν β).contDiffAt ((hO ν β).mem_nhds (hactiveO ν β ⟨hx,hm⟩))).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hEzero ν β x hx hm)).contDiffWithinAt
  have hU : ContDiffOn ℝ ∞ U Omega := ContDiffOn.sum fun ν _ => ContDiffOn.sum fun β _ => hfull ν β
  have hdiff (ν : Label) (β : Sub) (x : X) (hx : x ∈ Omega) :
      DifferentiableAt ℝ (fun y => waves ν β (kappa (x.1,y))) x.2 := by
    have hh := actual_joint_contDiffOn_slice (waves ν β ∘ kappa) Omega (hfull ν β) x.1
    exact (hh.contDiffAt ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hx)).differentiableAt (by simp)
  have he : EqOn (actualJointMetricLinearization Fobs U) (fun x => ∑ ν, ∑ β, E ν β x) Omega := by
    intro x hx
    have hd (ν : Label) : DifferentiableAt ℝ (fun y => ∑ β, waves ν β (kappa (x.1,y))) x.2 :=
      DifferentiableAt.fun_sum fun β _ => hdiff ν β x hx
    change actualCoordinateMetricLinearization (fun y => Fobs (x.1,y))
      (fun y => ∑ ν, ∑ β, waves ν β (kappa (x.1,y))) x.2 = _
    rw [actual_coordinate_metric_linearization_sum Finset.univ _ _ x.2 (fun ν _ => hd ν)]
    apply Finset.sum_congr rfl
    intro ν _
    exact actual_coordinate_metric_linearization_sum Finset.univ _ _ x.2 (fun β _ => hdiff ν β x hx)
  have hE : ContDiffOn ℝ ∞ (actualJointMetricLinearization Fobs U) Omega :=
    (ContDiffOn.sum fun ν _ => ContDiffOn.sum fun β _ => hEfull ν β).congr he
  have hEb : ∀ r ≤ j, ∀ x ∈ S,
      tau^r * ‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs U) x‖ ≤ ((L*R:ℕ):ℝ)*Budget := by
    intro r hr x hx
    let active := Finset.univ.filter (fun p : Label × Sub => kappa x ∈ Ksub p.1 p.2)
    have hactive : active.card ≤ L*R := actual_primary_active_pair_card_le K Ksub hsub (kappa x) L R
      (hL x hx) (fun ν => hR ν x hx)
    have hsm (p : Label × Sub) : ContDiffAt ℝ ∞ (E p.1 p.2) x :=
      (hEfull p.1 p.2).contDiffAt (hOmega.mem_nhds (hSOmega hx))
    have hno : ∀ p ∉ active, E p.1 p.2 =ᶠ[𝓝 x] fun _ => 0 := by
      intro p hp
      apply hEzero p.1 p.2 x (hSOmega hx)
      intro hm
      exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)
    have hb : ∀ p ∈ active, ‖iteratedFDeriv ℝ r (E p.1 p.2) x‖ ≤ Budget/tau^r := by
      intro p hp
      apply (le_div_iff₀ (pow_pos htau r)).mpr
      simpa only [mul_comm] using hbound p.1 p.2 r hr x ⟨hx,(Finset.mem_filter.mp hp).2⟩
    have hh := parameter_finite_sum_jet_le (fun p : Label × Sub => E p.1 p.2) x active (L*R) r
      (Budget/tau^r) hactive (by positivity) (fun p _ => hsm p) hno hb
    have hg : actualJointMetricLinearization Fobs U =ᶠ[𝓝 x] (fun y => ∑ p : Label × Sub, E p.1 p.2 y) := by
      filter_upwards [hOmega.mem_nhds (hSOmega hx)] with y hy
      simpa only [Fintype.sum_prod_type] using he hy
    rw [(hg.iteratedFDeriv ℝ r).eq_of_nhds]
    exact (mul_le_mul_of_nonneg_left hh (pow_nonneg htau.le r)).trans_eq
      (by field_simp [(pow_pos htau r).ne'])
  refine ⟨hU,hE,?_⟩
  intro delta r hr x hx
  have hde : EqOn (actualJointMetricLinearization Fobs (fun y => delta • U y))
      (fun y => delta • actualJointMetricLinearization Fobs U y) Omega := by
    intro y hy
    have hd := (actual_joint_contDiffOn_slice U Omega hU y.1).contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hy)
    ext v w
    simp only [actualJointMetricLinearization,actualCoordinateMetricLinearization_apply,
      fderiv_fun_const_smul (hd.differentiableAt (by simp)) delta,
      ContinuousLinearMap.smul_apply,inner_smul_right,real_inner_smul_left]
    ring
  have hg := hde.eventuallyEq_of_mem (hOmega.mem_nhds (hSOmega hx))
  rw [(hg.iteratedFDeriv ℝ r).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' ((hE.contDiffAt (hOmega.mem_nhds (hSOmega hx))).of_le
      (by simp : (r:ℕ∞ω) ≤ ∞)),norm_smul,Real.norm_eq_abs]
  calc
    _ = |delta| * (tau^r * ‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs U) x‖) := by ring
    _ ≤ |delta| * (((L*R:ℕ):ℝ)*Budget) := mul_le_mul_of_nonneg_left (hEb r hr x hx) (abs_nonneg delta)
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_physical_sum_weighted_jets
