import Smoothing.Round3OuterFixedCarrier
import Probes.Round3ParameterChartPullback

/-! The fixed-carrier plateau has the literal constant-one germ on the
original primary cutoff support. All derivatives of the actual modified eta
therefore agree with those of the original eta on every genuine native chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem round4_fixed_carrier_cutoff_germ {Z A : Type*} [TopologicalSpace Z] [Fintype A]
    (eta : A → Z → ℝ) (a : A) (z : Z)
    (hSum : ∀ᶠ w in 𝓝 z, ∑ b, eta b w = 1) :
    round3FixedCarrierCutoff eta a =ᶠ[𝓝 z] eta a := by
  filter_upwards [hSum] with w hw
  change Real.smoothTransition (4*(∑ b,eta b w)^2-1)*eta a w = eta a w
  rw [hw,Real.smoothTransition.one_of_one_le (by norm_num)]
  exact one_mul _

theorem round4_fixed_carrier_composed_jet {E Z A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Z] [Fintype A]
    (eta : A → Z → ℝ) (a : A) (f : E → Z) (x : E) (hf : ContinuousAt f x)
    (hSum : ∀ᶠ w in 𝓝 (f x), ∑ b, eta b w = 1) (j : ℕ) :
    iteratedFDeriv ℝ j (round3FixedCarrierCutoff eta a ∘ f) x =
      iteratedFDeriv ℝ j (eta a ∘ f) x :=
  (((round4_fixed_carrier_cutoff_germ eta a (f x) hSum).comp_tendsto hf).iteratedFDeriv ℝ j).eq_of_nhds

theorem round4_parameter_native_inverse_continuousAt
    {Ep D P M : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace P] [TopologicalSpace M]
    (B : OpenPartialHomeomorph P Ep) (a : OpenPartialHomeomorph (P × M) (P × D))
    (ha : Round3ParameterChartPreserves a) (z : Ep × D)
    (hz : z ∈ (round3ParameterChartPullback B a).target) :
    ContinuousAt (fun y : Ep × D =>
      (B.symm ((round3ParameterChartPullback B a).symm y).1,
        ((round3ParameterChartPullback B a).symm y).2)) z := by
  let aN := round3ParameterChartPullback B a
  have hinv : ContinuousAt aN.symm z := aN.symm.continuousOn.continuousAt (aN.open_target.mem_nhds hz)
  have hp : (aN.symm z).1 ∈ B.target := by
    rw [round3ParameterChartPreserves_inverse aN (round3ParameterChartPullback_preserves B a ha) z hz]
    exact ((round3ParameterChartPullback_target B a z).mp hz).1
  have hB : ContinuousAt B.symm (aN.symm z).1 :=
    B.symm.continuousOn.continuousAt (B.open_target.mem_nhds hp)
  exact (hB.comp (f := fun y : Ep × D => (aN.symm y).1) hinv.fst).prodMk hinv.snd

theorem round4_fixed_carrier_native_eta_jet
    {Ep D P M A : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace P] [TopologicalSpace M] [Fintype A]
    (B : OpenPartialHomeomorph P Ep) (chart : OpenPartialHomeomorph (P × M) (P × D))
    (ha : Round3ParameterChartPreserves chart) (eta : A → P × M → ℝ) (a : A)
    (z : Ep × D) (hz : z ∈ (round3ParameterChartPullback B chart).target)
    (hSum : ∀ᶠ w in 𝓝
      (B.symm ((round3ParameterChartPullback B chart).symm z).1,
        ((round3ParameterChartPullback B chart).symm z).2), ∑ b, eta b w = 1) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y : Ep × D => round3FixedCarrierCutoff eta a
      (B.symm ((round3ParameterChartPullback B chart).symm y).1,
        ((round3ParameterChartPullback B chart).symm y).2)) z =
    iteratedFDeriv ℝ j (fun y : Ep × D => eta a
      (B.symm ((round3ParameterChartPullback B chart).symm y).1,
        ((round3ParameterChartPullback B chart).symm y).2)) z :=
  round4_fixed_carrier_composed_jet eta a _ z
    (round4_parameter_native_inverse_continuousAt B chart ha z hz) hSum j

#print axioms round4_fixed_carrier_native_eta_jet
end GlobalEmbedding.Continuation
