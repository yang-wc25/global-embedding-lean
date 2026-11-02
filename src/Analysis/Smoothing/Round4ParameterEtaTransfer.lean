import Probes.Round3ParameterChartPullback
import Probes.ActualJointChartTransfer
import Smoothing.TensorProductJets

/-! Actual target-coordinate eta under a nontrivial parameter chart change.
The exact chart conjugation is retained. Only positive parameter transition
jets are used; no bound on arbitrary phase/chart values is inferred. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {Ep D M : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace M]
local notation "X" => Ep × D

theorem round4_positive_identity_jet_norm_le (k : ℕ) (hk : 1 ≤ k) (x : D) :
    ‖iteratedFDeriv ℝ k (id : D → D) x‖ ≤ 1 := by
  change ‖iteratedFDeriv ℝ k (ContinuousLinearMap.id ℝ D) x‖ ≤ 1
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  cases r with
  | zero =>
    simp only [norm_iteratedFDeriv_one,ContinuousLinearMap.fderiv]
    exact ContinuousLinearMap.norm_id_le
  | succ r =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (ContinuousLinearMap.id ℝ D) = fun _ : D => ContinuousLinearMap.id ℝ D :=
      funext (fun y => (ContinuousLinearMap.id ℝ D).fderiv)
    rw [he,iteratedFDeriv_const_of_ne (by omega : r+1 ≠ 0)]
    simp

theorem round4_parameter_change_joint_jet
    (C : OpenPartialHomeomorph Ep Ep) (hC : ContDiffOn ℝ ∞ C.symm C.target)
    (z : X) (hz : z.1 ∈ C.target) (T : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hjet : ‖iteratedFDeriv ℝ k C.symm z.1‖ ≤ T k) :
    ‖iteratedFDeriv ℝ k (fun y : X => (C.symm y.1,y.2)) z‖ ≤ max (T k) 1 := by
  exact tensor_product_map_jet_le C.open_target isOpen_univ hC
    (contDiff_id.contDiffOn) hz (mem_univ z.2) k (T k) 1 hjet
      (round4_positive_identity_jet_norm_le k hk z.2)

theorem round4_parameter_eta_pullback_germ
    (C : OpenPartialHomeomorph Ep Ep) (a : OpenPartialHomeomorph (Ep × M) X)
    (ha : Round3ParameterChartPreserves a) (eta : Ep × M → ℝ)
    (z : X) (hz : z ∈ (round3ParameterChartPullback C a).target) :
    (fun y : X => eta (C.symm ((round3ParameterChartPullback C a).symm y).1,
      ((round3ParameterChartPullback C a).symm y).2)) =ᶠ[𝓝 z]
      (eta ∘ a.symm) ∘ (fun y : X => (C.symm y.1,y.2)) := by
  let aN := round3ParameterChartPullback C a
  have haN := round3ParameterChartPullback_preserves C a ha
  filter_upwards [aN.open_target.mem_nhds hz] with y hy
  have ht := (round3ParameterChartPullback_target C a y).mp hy
  have hn := round3ParameterChartPreserves_inverse aN haN y hy
  have ho := round3ParameterChartPreserves_inverse a ha (C.symm y.1,y.2) ht.2.1
  apply congrArg eta
  apply Prod.ext
  · exact (congrArg C.symm hn).trans ho.symm
  · rfl

theorem round4_parameter_eta_pullback_slow_jet
    (C : OpenPartialHomeomorph Ep Ep) (hC : ContDiffOn ℝ ∞ C.symm C.target)
    (a : OpenPartialHomeomorph (Ep × M) X) (ha : Round3ParameterChartPreserves a)
    (eta : Ep × M → ℝ) (heta : ContDiffOn ℝ ∞ (eta ∘ a.symm) a.target)
    (T : ℕ → ℝ) (j : ℕ) (ell B : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (z : X) (hz : z ∈ (round3ParameterChartPullback C a).target)
    (hOuter : ∀ k ≤ j, ell^k*‖iteratedFDeriv ℝ k (eta ∘ a.symm) (C.symm z.1,z.2)‖ ≤ B)
    (hInner : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k C.symm z.1‖ ≤ T k) :
    ell^j*‖iteratedFDeriv ℝ j (fun y : X =>
      eta (C.symm ((round3ParameterChartPullback C a).symm y).1,
        ((round3ParameterChartPullback C a).symm y).2)) z‖ ≤
      actualFastChartTransferCost (fun k => max (T k) 1) j * B := by
  let aN := round3ParameterChartPullback C a
  let trans : X → X := fun y => (C.symm y.1,y.2)
  have hT (k : ℕ) : 0 ≤ max (T k) 1 := zero_le_one.trans (le_max_right _ _)
  have hSmooth : ContDiffOn ℝ ∞ trans aN.target := by
    exact (hC.comp contDiff_fst.contDiffOn
      (fun y hy => ((round3ParameterChartPullback_target C a y).mp hy).1)).prodMk
        contDiff_snd.contDiffOn
  have hMaps : MapsTo trans aN.target a.target :=
    fun y hy => ((round3ParameterChartPullback_target C a y).mp hy).2.1
  have ht := (round3ParameterChartPullback_target C a z).mp hz
  have hJets : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k trans z‖ ≤ max (T k) 1 := by
    intro k hk hkj
    exact (mul_le_mul_of_nonneg_left
      (round4_parameter_change_joint_jet C hC z ht.1 T k hk (hInner k hk hkj))
      (pow_nonneg hell.le _)).trans (mul_le_of_le_one_left (hT k)
        (pow_le_one₀ hell.le hell1))
  have hb := actual_fast_joint_chart_transfer (fun k => max (T k) 1) hT j
    trans (eta ∘ a.symm) aN.target a.target aN.open_target a.open_target
    hSmooth heta hMaps z hz ell ell B hell le_rfl hOuter hJets
  rw [((round4_parameter_eta_pullback_germ C a ha eta z hz).iteratedFDeriv ℝ j).eq_of_nhds]
  exact hb

#print axioms round4_parameter_eta_pullback_slow_jet
end GlobalEmbedding.Continuation
