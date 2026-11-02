import GlobalEmbedding.Paper.MatrixAnalyticFiniteCriticalSet
import GlobalEmbedding.Paper.MatrixUniformCriticalCutoffMass
import GlobalEmbedding.Paper.MatrixPeriodicNonstationaryCosBound
import GlobalEmbedding.Paper.MatrixSmoothCriticalCutoffQuotient
import GlobalEmbedding.Paper.MatrixCompactTimeDerivativeBound
import GlobalEmbedding.Paper.MatrixCriticalCutoffCosBound

/-!
# Actual compact-uniform decay for nonlinear periodic cosine phases

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line293.
DAG node: `matrix-compact-uniform-oscillatory-cos-average`.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Actual smooth joint families restrict to actual globally smooth time slices. -/
private theorem smooth_time_slice
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} (F : P × ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {p : P} (hp : p ∈ U) : ContDiff ℝ ∞ (fun t ↦ F (p, t)) := by
  apply contDiffOn_univ.mp
  exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ ↦ ⟨hp, mem_univ _⟩)

/-- Actual compact-uniform nonlinear oscillatory decay, from actual analytic
nonconstant period-one phase fibers and actual smooth joint data.

Proof: the actual time derivative H is jointly smooth. Analytic nonconstancy
makes each actual period-critical set finite/null. Native Dini gives uniform
smallness of the actual critical-region cutoff masses. The actual amplitude
bounds the near-critical contribution by a common M times those masses.
For fixed cutoff n, the actual quotient a·χ(nH²−1)/H is jointly smooth; actual
compactness bounds its actual time derivative uniformly. Periodic integration
by parts bounds the far-critical contribution by C_n/T. Choose n first for
the desired error, then T, and add the two genuine integrable pieces.
Source: `prop:matrix`, line293, uniform oscillatory cutoff argument. -/
theorem compact_uniform_oscillatory_cos_average
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U K : Set P} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (φ a : P × ℝ → ℝ)
    (hφ : ContDiffOn ℝ ∞ φ (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ univ))
    (hφperiod : ∀ p ∈ U, Function.Periodic (fun t ↦ φ (p, t)) 1)
    (haperiod : ∀ p ∈ U, Function.Periodic (fun t ↦ a (p, t)) 1)
    (hanalytic : ∀ p ∈ K, AnalyticOnNhd ℝ (fun t ↦ φ (p, t)) univ)
    (hnonconstant : ∀ p ∈ K, ∃ x y : ℝ, φ (p, x) ≠ φ (p, y))
    (phase : ℝ) :
    TendstoUniformlyOn
      (fun T : ℝ ↦ fun p : P ↦ ∫ t in Icc (0 : ℝ) 1,
        a (p, t) * Real.cos (T * φ (p, t) + phase))
      (fun _ : P ↦ (0 : ℝ)) atTop K := by
  let H : P × ℝ → ℝ := fun z ↦ deriv (fun t ↦ φ (z.1, t)) z.2
  have hH : ContDiffOn ℝ ∞ H (U ×ˢ univ) := contDiffOn_time_derivative hU φ hφ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : K × ℝ → P × ℝ := fun z ↦ (z.1.val, z.2)
  have hr : Continuous r := continuous_subtype_val.prodMap continuous_id
  have hrU : ∀ z, r z ∈ U ×ˢ (univ : Set ℝ) := fun z ↦ ⟨hKU z.1.property, mem_univ _⟩
  have hHr : Continuous (fun z : K × ℝ ↦ H (r z)) :=
    hH.continuousOn.comp_continuous hr hrU
  have har : Continuous (fun z : K × ℝ ↦ a (r z)) :=
    ha.continuousOn.comp_continuous hr hrU
  have hmass := uniform_critical_cutoff_mass (fun z : K × ℝ ↦ H (r z)) hHr
    (fun p ↦ (analytic_finite_critical_set (fun t ↦ φ (p.val, t))
      (hanalytic p.val p.property) (hnonconstant p.val p.property) 0 1).2)
  obtain ⟨M, hM, hnear⟩ := critical_cutoff_cos_bound
    (fun z : K × ℝ ↦ a (r z)) (fun z : K × ℝ ↦ H (r z)) har hHr
    (fun z : K × ℝ ↦ φ (r z))
  let B (n : ℕ) : P × ℝ → ℝ :=
    fun z ↦ a z * Real.smoothTransition ((n : ℝ) * H z ^ 2 - 1)
  let G (n : ℕ) : P × ℝ → ℝ := fun z ↦ B n z / H z
  have hBG (n : ℕ) := smooth_critical_cutoff_quotient (hU.prod isOpen_univ) H a hH ha n
  have hfar (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ T : ℝ, 0 < T →
      |∫ t in Icc (0 : ℝ) 1, B n (p, t) * Real.cos (T * φ (p, t) + phase)| ≤ C / T := by
    have hGn : ContDiffOn ℝ ∞ (G n) (U ×ˢ univ) := (hBG n).2.1
    obtain ⟨C, hC, hbound⟩ := compact_time_derivative_bound hU hK hKU (G n) hGn 0 1
    refine ⟨C, hC, ?_⟩
    intro p hp T hT
    have hpU := hKU hp
    have hφp := smooth_time_slice φ hφ hpU
    have hap := smooth_time_slice a ha hpU
    have hHp : ContDiff ℝ ∞ (fun t ↦ H (p, t)) := smooth_time_slice H hH hpU
    have hBp : ContDiff ℝ ∞ (fun t ↦ B n (p, t)) := smooth_time_slice (B n) (hBG n).1 hpU
    have hGp := smooth_time_slice (G n) hGn hpU
    have hHperiod : Function.Periodic (fun t ↦ H (p, t)) 1 := by
      intro t
      change deriv (fun s ↦ φ (p, s)) (t + 1) = deriv (fun s ↦ φ (p, s)) t
      rw [← deriv_comp_add_const]
      exact congrArg (fun f : ℝ → ℝ ↦ deriv f t) (funext (hφperiod p hpU))
    have hBperiod : Function.Periodic (fun t ↦ B n (p, t)) 1 := by
      intro t
      simp only [B, haperiod p hpU t, hHperiod t]
    have haway : ∀ t, deriv (fun s ↦ φ (p, s)) t = 0 →
        t ∉ tsupport (fun s ↦ B n (p, s)) := by
      have hc := smooth_critical_cutoff_quotient isOpen_univ
        (fun t ↦ H (p, t)) (fun t ↦ a (p, t))
        hHp.contDiffOn hap.contDiffOn n
      intro t ht
      exact hc.2.2.1 t (mem_univ _) ht
    have hi := periodic_nonstationary_cos_bound (fun t ↦ φ (p, t))
      (fun t ↦ B n (p, t)) hφp hBp (hφperiod p hpU) hBperiod haway T hT phase
    have hderivcont : Continuous (deriv (fun t ↦ G n (p, t))) :=
      (contDiff_infty_iff_deriv.mp hGp).2.continuous
    have hint : (∫ t in Icc (0 : ℝ) 1, |deriv (fun s ↦ G n (p, s)) t|) ≤ C := by
      calc
        _ ≤ ∫ _ in Icc (0 : ℝ) 1, C :=
          setIntegral_mono_on hderivcont.abs.continuousOn.integrableOn_Icc
            (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc
            (fun t ht ↦ by simpa only [Real.norm_eq_abs] using hbound p hp t ht)
        _ = C := by simp
    exact hi.trans (div_le_div_of_nonneg_right hint hT.le)
  rw [tendstoUniformlyOn_iff_restrict]
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  have hδ : 0 < ε / (2 * (M + 1)) := div_pos hε (by positivity)
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformly_iff.mp hmass) _ hδ).exists
  obtain ⟨C, hC, hCn⟩ := hfar n
  filter_upwards [eventually_gt_atTop (max 0 (2 * C / ε))] with T hT
  have hTpos : 0 < T := lt_of_le_of_lt (le_max_left _ _) hT
  have hfarSmall : C / T < ε / 2 := by
    have hthreshold : 2 * C / ε < T := lt_of_le_of_lt (le_max_right _ _) hT
    have hmul := (div_lt_iff₀ hε).mp hthreshold
    apply (div_lt_iff₀ hTpos).2
    nlinarith
  intro p
  change dist 0 (∫ t in Icc (0 : ℝ) 1, a (p.val, t) *
    Real.cos (T * φ (p.val, t) + phase)) < ε
  rw [dist_comm, Real.dist_eq, sub_zero]
  have hpU := hKU p.property
  have hφp := smooth_time_slice φ hφ hpU
  have hBp := smooth_time_slice (B n) (hBG n).1 hpU
  have hap := smooth_time_slice a ha hpU
  have hφpc : Continuous (fun t ↦ φ (p.val, t)) := hφp.continuous
  have hapc : Continuous (fun t ↦ a (p.val, t)) := hap.continuous
  have hcos : Continuous (fun t ↦ Real.cos (T * φ (p.val, t) + phase)) :=
    Real.continuous_cos.comp ((continuous_const.mul hφpc).add continuous_const)
  have hnearcont : Continuous (fun t ↦
      (a (p.val, t) * (1 - Real.smoothTransition ((n : ℝ) * H (p.val, t) ^ 2 - 1))) *
        Real.cos (T * φ (p.val, t) + phase)) := by
    have hHpc : Continuous (fun t ↦ H (p.val, t)) :=
      (smooth_time_slice H hH hpU).continuous
    exact (hapc.mul (continuous_const.sub (Real.smoothTransition.continuous.comp
      ((continuous_const.mul (hHpc.pow 2)).sub continuous_const)))).mul hcos
  have hsplit : (∫ t in Icc (0 : ℝ) 1, a (p.val, t) *
      Real.cos (T * φ (p.val, t) + phase)) =
      (∫ t in Icc (0 : ℝ) 1,
        (a (p.val, t) * (1 - Real.smoothTransition ((n : ℝ) * H (p.val, t) ^ 2 - 1))) *
          Real.cos (T * φ (p.val, t) + phase)) +
      (∫ t in Icc (0 : ℝ) 1, B n (p.val, t) *
        Real.cos (T * φ (p.val, t) + phase)) := by
    calc
      _ = ∫ t in Icc (0 : ℝ) 1,
          (a (p.val, t) * (1 - Real.smoothTransition ((n : ℝ) * H (p.val, t) ^ 2 - 1))) *
            Real.cos (T * φ (p.val, t) + phase) +
          B n (p.val, t) * Real.cos (T * φ (p.val, t) + phase) := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [B]
        ring
      _ = _ := integral_add hnearcont.continuousOn.integrableOn_Icc
        (hBp.continuous.mul hcos).continuousOn.integrableOn_Icc
  have hmassSmall : (∫ t in Icc (0 : ℝ) 1,
      1 - Real.smoothTransition ((n : ℝ) * H (p.val, t) ^ 2 - 1)) <
      ε / (2 * (M + 1)) := by
    have h := hn p
    simp only [Real.dist_eq, zero_sub, abs_neg] at h
    exact (le_abs_self _).trans_lt h
  have hnearSmall : M * (∫ t in Icc (0 : ℝ) 1,
      1 - Real.smoothTransition ((n : ℝ) * H (p.val, t) ^ 2 - 1)) < ε / 2 := by
    have hproduct := mul_le_mul_of_nonneg_left (le_of_lt hmassSmall) hM
    have hsmall : M * (ε / (2 * (M + 1))) < ε / 2 := by
      have hpos : 0 < M + 1 := by positivity
      calc
        _ < (M + 1) * (ε / (2 * (M + 1))) :=
          mul_lt_mul_of_pos_right (by linarith) hδ
        _ = ε / 2 := by field_simp [hpos.ne']
    exact hproduct.trans_lt hsmall
  rw [hsplit]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ M * (∫ t in Icc (0 : ℝ) 1,
          1 - Real.smoothTransition ((n : ℝ) * H (p.val, t) ^ 2 - 1)) + C / T :=
      add_le_add (hnear n T phase p) (hCn p.val p.property T hTpos)
    _ < ε := by linarith

#print axioms compact_uniform_oscillatory_cos_average

end GlobalEmbedding.Paper
