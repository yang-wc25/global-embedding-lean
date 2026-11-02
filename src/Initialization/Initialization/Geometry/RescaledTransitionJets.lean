import Initialization.Geometry.BoundedScaledAtlas
import Initialization.Geometry.CoordinateExtensionJets
import Initialization.Geometry.CenteredRescaling
import Initialization.Geometry.UniformSupportDegree

/-!
# Uniform actual transition jets on fixed-radius scale atlases

Every transition is the actual composition of the actual native charts.
The proof identifies its germ with a globally extended fixed-coordinate map,
then applies the exact T·T⁻ʲ scaling. All constants are selected from the fixed
compact chart preparation before T; arbitrary off-domain chart values are unused.
-/

open Set Metric Filter Manifold IsManifold Topology Function
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization

/-- Exact positive-order jet scaling for an affine-rescaled transition. -/
theorem iteratedFDeriv_rescaled_transition
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p : E) (q : F) {T : ℝ} (hT : T ≠ 0)
    {j : ℕ} (hj : j ≠ 0) (y : E)
    (hf : ContDiffAt ℝ j f (p + T⁻¹ • y)) :
    iteratedFDeriv ℝ j (fun z ↦ T • (f (p + T⁻¹ • z) - q)) y =
      T • ((T⁻¹) ^ j • iteratedFDeriv ℝ j f (p + T⁻¹ • y)) := by
  have ha : ContDiffAt ℝ j (fun z : E ↦ p + T⁻¹ • z) y :=
    contDiffAt_const.add (contDiffAt_const.smul contDiffAt_id)
  have hh : ContDiffAt ℝ j (fun z ↦ f (p + T⁻¹ • z) - q) y :=
    (hf.comp y ha).sub contDiffAt_const
  rw [iteratedFDeriv_const_smul_apply' hh,
    iteratedFDeriv_centered_rescaling (fun z ↦ f z - q) p hT,
    iteratedFDeriv_sub_fixed_center f q hj _ hf]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

/-- The fixed preparation itself supplies all-order transition bounds on the
entire genuine overlap domains of the bounded rescaled atlas, uniformly in T.
No transition derivative sequence or coordinate comparison is an input. -/
theorem exists_uniform_boundedAtlas_transition_bounds (G : PreparedCharts M n) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ T : ℝ, ∀ hT : 1 ≤ T, ∀ F : ChartCutoffFamily G T,
        ∀ (i k : Fin F.count) (j : ℕ) (y : EuclideanSpace ℝ (Fin n)),
          y ∈ (((F.boundedAtlas hT).chart i).symm.trans
          ((F.boundedAtlas hT).chart k)).source →
        ‖iteratedFDeriv ℝ j
          ((F.boundedAtlas hT).chart k ∘ ((F.boundedAtlas hT).chart i).symm) y‖ ≤ B j := by
  obtain ⟨ext, C, hC, hext, heq, hjets⟩ := exists_prepared_coordinate_extension_jets G
  refine ⟨fun j ↦ C j + G.scaleRadius, fun j ↦ add_pos_of_nonneg_of_pos (hC j) G.scaleRadius_pos, ?_⟩
  intro T hT F i k j y hy
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hyt : y ∈ ((F.boundedAtlas hT).chart i).target := hy.1
  have hxk : ((F.boundedAtlas hT).chart i).symm y ∈ ((F.boundedAtlas hT).chart k).source := hy.2
  by_cases hj : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero]
    have htarget := ((F.boundedAtlas hT).chart k).map_source hxk
    have hn : ‖(F.boundedAtlas hT).chart k (((F.boundedAtlas hT).chart i).symm y)‖ < G.scaleRadius := by
      simpa only [F.boundedAtlas_target hT k, mem_ball, dist_zero_right] using htarget
    exact hn.le.trans (le_add_of_nonneg_left (hC 0))
  · have hxcore := F.boundedAtlas_source_in_open_core hT k hxk
    have hxe : ((F.boundedAtlas hT).chart i).symm y ∈ (G.chart (F.parent k)).source := hxk.1
    have he := prepared_coordinate_extension_eventuallyEq G ext heq (F.parent k) hxe hxcore
    have he' := he.comp_tendsto (((F.boundedAtlas hT).chart i).symm.continuousAt hyt)
    let base := ext (F.parent k) ∘ (G.chart (F.parent i)).symm
    have hgerm :
        ((F.boundedAtlas hT).chart k ∘ ((F.boundedAtlas hT).chart i).symm) =ᶠ[𝓝 y]
        (fun z ↦ T • (base (F.center i + T⁻¹ • z) - F.center k)) := by
      filter_upwards [he'] with z hz
      change T • (G.chart (F.parent k)
        ((G.chart (F.parent i)).symm (T⁻¹ • z + F.center i)) - F.center k) = _
      change ext (F.parent k) ((G.chart (F.parent i)).symm (T⁻¹ • z + F.center i)) =
        G.chart (F.parent k) ((G.chart (F.parent i)).symm (T⁻¹ • z + F.center i)) at hz
      rw [← hz]
      simp only [base, Function.comp_apply, add_comm]
    have hycore : F.center i + T⁻¹ • y ∈
        ball (G.center (F.parent i)) (2 * G.radius (F.parent i)) :=
      F.scaledPoint_in_open_core hT i hyt
    have hyparent : F.center i + T⁻¹ • y ∈ (G.chart (F.parent i)).target :=
      G.buffered _ ((closedBall_subset_closedBall (by linarith [G.radius_pos (F.parent i)]))
        (ball_subset_closedBall hycore))
    have hbase : ContDiffOn ℝ ∞ base (G.chart (F.parent i)).target :=
      ((hext (F.parent k)).comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas (G.chart_smooth (F.parent i)))).contDiffOn
    have hb : ContDiffAt ℝ j base (F.center i + T⁻¹ • y) :=
      (hbase.contDiffAt ((G.chart (F.parent i)).open_target.mem_nhds hyparent)).of_le (by simp)
    rw [(hgerm.iteratedFDeriv ℝ j).eq_of_nhds,
      iteratedFDeriv_rescaled_transition base (F.center i) (F.center k) hTpos.ne' hj y hb,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hTpos,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
    have hfactor : T * (T⁻¹) ^ j ≤ 1 := by
      calc
        T * (T⁻¹) ^ j ≤ T * T⁻¹ := mul_le_mul_of_nonneg_left
          (pow_le_of_le_one (inv_nonneg.mpr hTpos.le) (inv_le_one_of_one_le₀ hT) hj) hTpos.le
        _ = 1 := mul_inv_cancel₀ hTpos.ne'
    have hjet : ‖iteratedFDeriv ℝ j base (F.center i + T⁻¹ • y)‖ ≤ C j :=
      hjets (F.parent i) (F.parent k) j _ (ball_subset_closedBall hycore)
    calc
      T * ((T⁻¹) ^ j * ‖iteratedFDeriv ℝ j base (F.center i + T⁻¹ • y)‖) ≤
          T * ((T⁻¹) ^ j * C j) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hjet (by positivity)) hTpos.le
      _ = (T * (T⁻¹) ^ j) * C j := by ring
      _ ≤ C j := mul_le_of_le_one_left (hC j) hfactor
      _ ≤ C j + G.scaleRadius := le_add_of_nonneg_right G.scaleRadius_pos.le

/-- A complete actual atlas geometry producer: fixed positive radius, fixed
support graph degree and fixed all-order transition sequence precede every T.
The original metric and coframe reference budgets are separate proven producers. -/
theorem exists_compact_uniform_bounded_scale_atlases :
    ∃ (G : PreparedCharts M n) (D : ℕ) (B : ℕ → ℝ),
      (∀ j, 0 < B j) ∧
      ∀ T : ℝ, ∀ hT : 1 ≤ T, ∃ F : ChartCutoffFamily G T,
        GlobalEmbedding.Paper.IsSmoothBufferedAtlas (F.boundedAtlas hT) ∧
        (∀ i, ((F.boundedAtlas hT).chart i).target = ball 0 G.scaleRadius) ∧
        (F.boundedAtlas hT).buffer = G.scaleRadius / 2 ∧
        (∀ i, IsCompact ((F.boundedAtlas hT).support i)) ∧
        (F.boundedAtlas hT).supportDegree ≤ D ∧
        ∀ (i k : Fin F.count) (j : ℕ) (y : EuclideanSpace ℝ (Fin n)),
          y ∈ (((F.boundedAtlas hT).chart i).symm.trans
          ((F.boundedAtlas hT).chart k)).source →
          ‖iteratedFDeriv ℝ j
            ((F.boundedAtlas hT).chart k ∘ ((F.boundedAtlas hT).chart i).symm) y‖ ≤ B j := by
  obtain ⟨G⟩ := exists_preparedCharts (M := M) (n := n)
  obtain ⟨D, hD⟩ := exists_uniform_enlargedSupport_degree G
  obtain ⟨B, hB, htrans⟩ := exists_uniform_boundedAtlas_transition_bounds G
  refine ⟨G, D, B, hB, ?_⟩
  intro T hT
  obtain ⟨F⟩ := exists_chartCutoffFamily G hT
  exact ⟨F, F.boundedAtlas_smooth hT, F.boundedAtlas_target hT, rfl,
    F.enlargedSupport_compact hT, hD T hT F, htrans T hT F⟩

end GlobalEmbedding.Initialization
