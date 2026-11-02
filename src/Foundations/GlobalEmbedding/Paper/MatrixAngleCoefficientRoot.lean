import GlobalEmbedding.Paper.MatrixAngleUniformHessian
import GlobalEmbedding.Paper.MatrixNativeAngleGram
import GlobalEmbedding.Paper.MatrixNativeAngleResidual
import GlobalEmbedding.Paper.MatrixUniformCorrectionFamily
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Actual small basic coefficient roots of the four-moment equation

Source: `main.tex`, `prop:matrix`, lines307–323.
DAG node: `matrix-angle-coefficient-root`; exclusive owner W2.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Set Filter MeasureTheory

namespace GlobalEmbedding.Paper

/-- The literal original four-moment equation has actual native smooth small roots,
uniformly tending to zero, and actual orbit-basic coefficient fields eventually.
All inverse, Hessian and residual estimates are obtained from the actual planar map. -/
theorem matrixAngleCoefficientRoot_exists {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ) :
    ∃ c : ℝ → PlanarHopfSphere C → MatrixAngleCoefficients,
      (∀ T, ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngleCoefficients) ∞ (c T)) ∧
      TendstoUniformly c (fun _ ↦ (0 : MatrixAngleCoefficients)) atTop ∧
      (∀ᶠ T : ℝ in atTop,
        (∀ z, matrixAngleMomentMap f (planarOrbitCurvature planarHopfFlow f) T z (c T z) = 0) ∧
        (∀ z s, c T (planarHopfFlow s z) = c T z)) := by
  classical
  let κ := planarOrbitCurvature planarHopfFlow f
  let H : ℝ → PlanarHopfSphere C → MatrixAngleCoefficients → MatrixAngleCoefficients :=
    matrixAngleMomentMap f κ
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf
  have ha := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hv
  have hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ :=
    planarOrbitCurvature_contMDiff planarHopfFlow f hv ha
  have hH (T : ℝ) : ContMDiff
      ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients))
      𝓘(ℝ, MatrixAngleCoefficients) ∞ (Function.uncurry (H T)) :=
    matrixAngleMomentMap_contMDiff f hf κ hκ T
  let residual : ℝ → C(PlanarHopfSphere C, MatrixAngleCoefficients) := fun T ↦
    ⟨fun z ↦ H T z 0, ((hH T).comp (contMDiff_id.prodMk contMDiff_const)).continuous⟩
  let ε : ℝ → ℝ := fun T ↦ ‖residual T‖
  have hres : ∀ T z, ‖H T z 0‖ ≤ ε T :=
    fun T z ↦ (residual T).norm_coe_le_norm z
  have hlim : Tendsto ε atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have h := (Metric.tendstoUniformly_iff.mp
      (matrix_angle_residual_tendsto_uniformly f hf hunit hana κ)) (δ / 2) (half_pos hδ)
    filter_upwards [h] with T hT
    have hb : ‖residual T‖ ≤ δ / 2 :=
      (ContinuousMap.norm_le _ (half_pos hδ).le).mpr fun z ↦ by
        change ‖matrixAngleMomentMap f κ T z 0‖ ≤ δ / 2
        simpa only [dist_zero_left, norm_neg] using (hT z).le
    have he : ε T < δ := hb.trans_lt (by linarith)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ ε T from norm_nonneg (residual T))] using he
  obtain ⟨δ, L, _, hL, hgram⟩ := matrix_angle_gram_uniform_inverse_bound f hf hunit hana
  obtain ⟨K, hK, hHess⟩ := matrixAngleMomentMap_native_uniform_hessian f hf
  let Good (T : ℝ) : Prop := ∀ z : PlanarHopfSphere C,
    ∃ e : MatrixAngleCoefficients ≃L[ℝ] MatrixAngleCoefficients,
      e.toContinuousLinearMap = matrixAngleGram f κ T z ∧ ‖e.symm.toContinuousLinearMap‖ ≤ L
  have hGood : ∀ᶠ T : ℝ in atTop, Good T := hgram.mono fun T hT z ↦ (hT z).2
  let A (T : ℝ) (z : PlanarHopfSphere C) :
      MatrixAngleCoefficients ≃L[ℝ] MatrixAngleCoefficients :=
    if h : Good T then Classical.choose (h z) else ContinuousLinearEquiv.refl ℝ _
  have hA (T : ℝ) (h : Good T) (z : PlanarHopfSphere C) :
      (A T z).toContinuousLinearMap = matrixAngleGram f κ T z ∧
        ‖(A T z).symm.toContinuousLinearMap‖ ≤ L := by
    simp only [A, dite_eq_left h]
    exact Classical.choose_spec (h z)
  let r : ℝ := (4 * L * (K + 1))⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : 4 * L * K * r ≤ 1 := by
    have he : 4 * L * (K + 1) * r = 1 := mul_inv_cancel₀ (by positivity)
    calc
      4 * L * K * r ≤ 4 * L * (K + 1) * r := by gcongr; linarith
      _ = 1 := he
  have hεL : Tendsto (fun T ↦ L * ε T) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have hεsmall := hεL.eventually (gt_mem_nhds (half_pos hr))
  have hdata : ∀ᶠ T : ℝ in atTop,
      0 ≤ ε T ∧ L * ε T ≤ r / 2 ∧
      ContMDiff ((planarHopfModel C).prod 𝓘(ℝ, MatrixAngleCoefficients))
        𝓘(ℝ, MatrixAngleCoefficients) ∞ (Function.uncurry (H T)) ∧
      (∀ z, (A T z : MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients) =
        fderiv ℝ (H T z) 0) ∧
      (∀ z, ‖(A T z).symm.toContinuousLinearMap‖ ≤ L) ∧
      (∀ z, ∀ a ∈ Metric.closedBall (0 : MatrixAngleCoefficients) r,
        ‖fderiv ℝ (fderiv ℝ (H T z)) a‖ ≤ K) ∧
      (∀ z, ‖H T z 0‖ ≤ ε T) := by
    filter_upwards [hGood, hεsmall] with T hT hεT
    refine ⟨norm_nonneg _, hεT.le, hH T, ?_, fun z ↦ (hA T hT z).2,
      fun z a _ ↦ hHess T z a, hres T⟩
    intro z
    exact (hA T hT z).1.trans (matrixAngleMomentMap_native_fderiv_zero f hf T z).symm
  obtain ⟨c, hc, hcdata, hclim⟩ := uniform_correction_family
    (P := EuclideanSpace ℝ (Fin (2 * C - 1))) atTop H A r L K ε
    hr hL hK hsmall hlim hdata
  refine ⟨c, hc, hclim, hcdata.mono ?_⟩
  intro T hT
  refine ⟨fun z ↦ (hT.1 z).1, fun z s ↦ ?_⟩
  exact hT.2 (planarHopfFlow s z) z (fun a ↦ matrixAngleMomentMap_flow f κ T z s a)

end GlobalEmbedding.Paper
