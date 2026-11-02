import Initialization.Assembly.ActualRateError

/-!
# Internally generated actual rate-error estimates

The zeroth discrepancy comes from actual coframe freezing and exact coordinate
naturality. Higher discrepancies are bounded by actual phase and coframe jets,
and retain T⁻¹. No phase-rate budget is an assumption of these producers.
-/

noncomputable section
open Bundle Manifold Set Metric Filter IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- The actual cross-chart rate error is O(K⁻¹), with one constant fixed before
both real parameters and before the actual net is selected. -/
theorem exists_actualPhaseRateError_zero_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K T : ℝ), ∀ hK : 1 ≤ K, ∀ hT : 1 ≤ T, ∀ F : ChartCutoffFamily G K,
      ∀ (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) i y,
        q + T⁻¹ • y ∈ closedBall (G.center p) (2 * G.radius p) →
        (G.chart p).symm (q + T⁻¹ • y) ∈ F.enlargedSupport i →
        ‖actualPhaseRateError G g f F p q T i y‖ ≤ C / K := by
  obtain ⟨ext, A, hA, _hext, heq, hjets⟩ := exists_prepared_coordinate_extension_jets G
  obtain ⟨C, _B, hC, _hB, hfreeze, _hfreezeJets⟩ := exists_actual_frozenCoframe_bounds G g f
  refine ⟨C * A 1, mul_nonneg hC.le (hA 1), ?_⟩
  intro K T hK hT F p q i y hy hx
  let u := q + T⁻¹ • y
  have hut : u ∈ (G.chart p).target :=
    G.buffered p ((closedBall_subset_closedBall (by linarith [G.radius_pos p])) hy)
  rw [actualPhaseRateError_eq_frozen_transition G g f F p q
    (zero_lt_one.trans_le hT).ne' i hut hx.1]
  have hb := hfreeze K hK F i _ hx
  rw [F.frozenVectorPhase_ownChart_fderiv G g f i
    ((G.chart (F.parent i)).map_source hx.1)] at hb
  have hgerm := (prepared_coordinate_extension_eventuallyEq G ext heq (F.parent i) hx.1
    (F.enlargedSupport_in_open_core hK i hx)).comp_tendsto
      ((G.chart p).symm.continuousAt hut)
  have hd : ‖fderiv ℝ (G.chart (F.parent i) ∘ (G.chart p).symm) u‖ ≤ A 1 := by
    rw [← hgerm.fderiv_eq]
    simpa only [norm_iteratedFDeriv_one] using hjets p (F.parent i) 1 u hy
  calc
    _ ≤ ‖preparedCoframe G g f (F.parent i) (F.center i) -
        preparedCoframe G g f (F.parent i)
          (G.chart (F.parent i) ((G.chart p).symm u))‖ *
        ‖fderiv ℝ (G.chart (F.parent i) ∘ (G.chart p).symm) u‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C / K) * A 1 := mul_le_mul hb hd (norm_nonneg _) (by positivity)
    _ = (C * A 1) / K := by ring

/-- Actual coframe reference jets have the exact inverse-dilation gain. -/
theorem exists_actualReferenceCoframe_jet_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 1 ≤ B j) ∧
      ∀ (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) (T : ℝ), 1 ≤ T → ∀ j y,
        q + T⁻¹ • y ∈ closedBall (G.center p) (2 * G.radius p) →
        ‖iteratedFDeriv ℝ j (actualReferenceCoframe G g f p q T) y‖ ≤ B j * (T⁻¹)^j := by
  obtain ⟨B, _L, hB, _hL, hcoef, _hinverse⟩ := exists_preparedCoframe_uniform_bounds G g f
  refine ⟨B, hB, ?_⟩
  intro p q T hT j y hy
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  change ‖iteratedFDeriv ℝ j (fun z ↦ preparedCoframe G g f p (q + T⁻¹ • z)) y‖ ≤ _
  rw [iteratedFDeriv_centered_rescaling _ q hTpos.ne', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
  exact (mul_le_mul_of_nonneg_left
    (hcoef j p _ ((closedBall_subset_closedBall (by linarith [G.radius_pos p])) hy))
    (by positivity)).trans_eq (mul_comm _ _)

/-- The actual rate error has the required all-order K⁻¹+K/T bound. The entire
constant sequence is generated before K,T; neither a map nor an estimate is
assumed. All estimates are on genuine overlaps, including support boundaries. -/
theorem exists_actualPhaseRateError_jet_bounds :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (K T : ℝ), ∀ hK : 1 ≤ K, ∀ hKT : K ≤ T, ∀ F : ChartCutoffFamily G K,
      ∀ (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) i j y,
        q + T⁻¹ • y ∈ closedBall (G.center p) (2 * G.radius p) →
        (G.chart p).symm (q + T⁻¹ • y) ∈ F.enlargedSupport i →
        ‖iteratedFDeriv ℝ j (actualPhaseRateError G g f F p q T i) y‖ ≤
          A j * (K⁻¹ + K / T) := by
  obtain ⟨C, hC, hzero⟩ := exists_actualPhaseRateError_zero_bound G g f
  obtain ⟨P, hP, hphase⟩ := exists_actual_frozenPhase_rescaled_bounds G g f
  obtain ⟨B, hB, hcoframe⟩ := exists_actualReferenceCoframe_jet_bounds G g f
  let A : ℕ → ℝ := fun j ↦ C + P (j+1) + B j + 1
  have hA (j : ℕ) : 0 < A j := by
    dsimp [A]
    linarith [hP (j+1), hB j]
  refine ⟨A, hA, ?_⟩
  intro K T hK hKT F p q i j y hy hx
  have hT := hK.trans hKT
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hut : q + T⁻¹ • y ∈ (G.chart p).target :=
    G.buffered p ((closedBall_subset_closedBall (by linarith [G.radius_pos p])) hy)
  by_cases hj : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero]
    calc
      _ ≤ C / K := hzero K T hK hT F p q i y hy hx
      _ ≤ A 0 / K := div_le_div_of_nonneg_right (by dsimp [A]; linarith [hP 1, hB 0]) hKpos.le
      _ ≤ A 0 * (K⁻¹ + K / T) := by
        rw [div_eq_mul_inv, mul_add]
        exact le_add_of_nonneg_right (mul_nonneg (hA 0).le (div_nonneg hKpos.le hTpos.le))
  · have hjpos : 1 ≤ j := by omega
    have hp := actualPhaseCoordinate_contDiffAt G g f F p q T i hut hx.1
    have hr := actualReferenceCoframe_contDiffAt G g f p q T hut
    have hd := hp.fderiv_right (m := ∞) (by simp)
    have he : ‖iteratedFDeriv ℝ j (actualPhaseRateError G g f F p q T i) y‖ ≤
        T * ‖iteratedFDeriv ℝ (j+1) (actualPhaseCoordinate G g f F p q T i) y‖ +
        ‖iteratedFDeriv ℝ j (actualReferenceCoframe G g f p q T) y‖ := by
      change ‖iteratedFDeriv ℝ j
        ((fun z ↦ T • fderiv ℝ (actualPhaseCoordinate G g f F p q T i) z) -
          actualReferenceCoframe G g f p q T) y‖ ≤ _
      rw [iteratedFDeriv_sub_apply ((hd.const_smul T).of_le (by simp)) (hr.of_le (by simp))]
      apply (norm_sub_le _ _).trans
      rw [iteratedFDeriv_const_smul_apply' (hd.of_le (by simp)), norm_smul,
        Real.norm_eq_abs, abs_of_pos hTpos, norm_iteratedFDeriv_fderiv]
    have hscale : T * (T⁻¹)^(j+1) = (T⁻¹)^j := by
      rw [pow_succ]
      field_simp
    calc
      _ ≤ T * ‖iteratedFDeriv ℝ (j+1) (actualPhaseCoordinate G g f F p q T i) y‖ +
          ‖iteratedFDeriv ℝ j (actualReferenceCoframe G g f p q T) y‖ := he
      _ ≤ T * (P (j+1) * (T⁻¹)^(j+1)) + B j * (T⁻¹)^j :=
        add_le_add (mul_le_mul_of_nonneg_left
          (hphase K T hK hT F p q i (j+1) (by omega) y hy hx).1 hTpos.le)
          (hcoframe p q T hT j y hy)
      _ = (P (j+1) + B j) * (T⁻¹)^j := by
        rw [mul_left_comm T, hscale]
        ring
      _ ≤ (P (j+1) + B j) * T⁻¹ := mul_le_mul_of_nonneg_left
        (pow_le_of_le_one (inv_nonneg.mpr hTpos.le) (inv_le_one_of_one_le₀ hT) (by omega))
        (by linarith [hP (j+1), hB j])
      _ ≤ A j * T⁻¹ := mul_le_mul_of_nonneg_right
        (by dsimp [A]; linarith) (inv_nonneg.mpr hTpos.le)
      _ ≤ A j * (K⁻¹ + K / T) := mul_le_mul_of_nonneg_left
        (by rw [div_eq_mul_inv]; nlinarith [inv_nonneg.mpr hKpos.le,
          inv_nonneg.mpr hTpos.le]) (hA j).le

end GlobalEmbedding.Initialization
