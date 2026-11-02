import Smoothing.Round4ParameterEtaTransfer

/-! The actual supported physical lift, observed through an arbitrary original
parameter chart. The if-branch and both nonlinear chart conjugations remain
literal. Positive transition jets suffice for every order of the eta budget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {Ep D M P : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace M] [TopologicalSpace P]
local notation "X" => Ep × D

theorem round4_physical_observer_eta_target
    (Bp Bo : OpenPartialHomeomorph P Ep) (a : OpenPartialHomeomorph (Ep × M) X)
    (ha : Round3ParameterChartPreserves a) (z : X)
    (hz : z ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm a)).target) :
    z ∈ (round3ParameterChartPullback (Bp.symm.trans Bo) a).target := by
  have ho := (round3ParameterChartPullback_target Bo (round3ParameterChartPullback Bp.symm a) z).mp hz
  have hp := (round3ParameterChartPullback_target Bp.symm a (Bo.symm z.1,z.2)).mp ho.2.1
  exact (round3ParameterChartPullback_target_iff (Bp.symm.trans Bo) a ha z
    ⟨ho.1,hp.1⟩).mpr hp.2.1

theorem round4_physical_observer_eta_germ
    (Bp Bo : OpenPartialHomeomorph P Ep) (a : OpenPartialHomeomorph (Ep × M) X)
    (ha : Round3ParameterChartPreserves a) (eta : Ep × M → ℝ)
    (z : X)
    (hz : z ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm a)).target) :
    let aN := round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm a)
    let etaP := fun w : P × M => if w.1 ∈ Bp.source then eta (Bp w.1,w.2) else 0
    (fun y : X => etaP (Bo.symm (aN.symm y).1,(aN.symm y).2)) =ᶠ[𝓝 z]
      (eta ∘ a.symm) ∘ (fun y : X => ((Bp.symm.trans Bo).symm y.1,y.2)) := by
  classical
  intro aN etaP
  have haN := round3ParameterChartPullback_preserves Bo
    (round3ParameterChartPullback Bp.symm a) (round3ParameterChartPullback_preserves Bp.symm a ha)
  filter_upwards [aN.open_target.mem_nhds hz] with y hy
  have ho := (round3ParameterChartPullback_target Bo (round3ParameterChartPullback Bp.symm a) y).mp hy
  have hp := (round3ParameterChartPullback_target Bp.symm a (Bo.symm y.1,y.2)).mp ho.2.1
  have hn := round3ParameterChartPreserves_inverse aN haN y hy
  have hi := round3ParameterChartPreserves_inverse a ha (Bp (Bo.symm y.1),y.2) hp.2.1
  have hSource : Bo.symm y.1 ∈ Bp.source := hp.1
  change (if Bo.symm (aN.symm y).1 ∈ Bp.source then
    eta (Bp (Bo.symm (aN.symm y).1),(aN.symm y).2) else 0) = _
  rw [hn,ite_eq_left hSource]
  apply congrArg eta
  apply Prod.ext
  · exact hi.symm
  · rfl

theorem round4_physical_observer_eta_slow_jet
    (Bp Bo : OpenPartialHomeomorph P Ep)
    (hC : ContDiffOn ℝ ∞ (Bp.symm.trans Bo).symm (Bp.symm.trans Bo).target)
    (a : OpenPartialHomeomorph (Ep × M) X) (ha : Round3ParameterChartPreserves a)
    (eta : Ep × M → ℝ) (heta : ContDiffOn ℝ ∞ (eta ∘ a.symm) a.target)
    (T : ℕ → ℝ) (j : ℕ) (ell B : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (z : X)
    (hz : z ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm a)).target)
    (hOuter : ∀ k ≤ j, ell^k*‖iteratedFDeriv ℝ k (eta ∘ a.symm)
      ((Bp.symm.trans Bo).symm z.1,z.2)‖ ≤ B)
    (hInner : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (Bp.symm.trans Bo).symm z.1‖ ≤ T k) :
    let aN := round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm a)
    let etaP := fun w : P × M => if w.1 ∈ Bp.source then eta (Bp w.1,w.2) else 0
    ell^j*‖iteratedFDeriv ℝ j (fun y : X =>
      etaP (Bo.symm (aN.symm y).1,(aN.symm y).2)) z‖ ≤
        actualFastChartTransferCost (fun k => max (T k) 1) j * B := by
  classical
  intro aN etaP
  have ht := round4_physical_observer_eta_target Bp Bo a ha z hz
  have hPhysical := round4_physical_observer_eta_germ Bp Bo a ha eta z hz
  have hNative := round4_parameter_eta_pullback_germ (Bp.symm.trans Bo) a ha eta z ht
  have he := hPhysical.trans hNative.symm
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact round4_parameter_eta_pullback_slow_jet (Bp.symm.trans Bo) hC a ha eta heta
    T j ell B hell hell1 z ht hOuter hInner

#print axioms round4_physical_observer_eta_slow_jet
end GlobalEmbedding.Continuation
