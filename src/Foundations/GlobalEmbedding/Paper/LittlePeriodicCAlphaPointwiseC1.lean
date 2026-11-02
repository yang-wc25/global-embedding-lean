import GlobalEmbedding.Paper.LittlePeriodicCAlphaComplete
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pointwise derivatives and continuous actual derivative data give norm-level C¹

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-pointwise-to-norm-c1`.
-/

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

namespace GlobalEmbedding.Paper

/-- An actual little Hölder family is genuinely C¹ if its candidate parameter derivative is
operator-norm continuous and gives the genuine pointwise derivatives along parameter lines.

Proof: continuity makes the candidate derivative norm-integrable on each straight segment.
Actual continuous evaluations commute with that Bochner integral, and pointwise FTC identifies
it with the actual family difference. Continuity of the candidate operator makes the resulting
Fréchet remainder ≤ε‖h‖ in the ORIGINAL norm. The C¹ derivative criterion completes the proof.
No norm differentiability or norm continuity of F is assumed. Source: smooth slices in
`lem:balanced`. -/
theorem littlePeriodicCAlpha_contDiff_one_of_pointwise
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {a N k : ℕ} {α : ℝ}
    (F : P → LittlePeriodicCAlphaFunction a N k α)
    (A : P → P →L[ℝ] LittlePeriodicCAlphaFunction a N k α) (hA : Continuous A)
    (hpoint : ∀ (p v : P) (x : EuclideanSpace ℝ (Fin a)) (t : ℝ),
      HasDerivAt (fun s : ℝ ↦ (F (p + s • v)).val.toFun x)
        ((A (p + t • v) v).val.toFun x) t) : ContDiff ℝ 1 F := by
  have hint (p h : P) : IntervalIntegrable (fun t : ℝ ↦ A (p + t • h) h) volume 0 1 :=
    ((hA.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable 0 1
  have hsegment (p h : P) : (∫ t : ℝ in 0..1, A (p + t • h) h) = F (p + h) - F p := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    obtain ⟨ev, hev, hnorm⟩ := collar_little_holder_evaluation (N := N) (k := k) (α := α) x
    have hcont : Continuous (fun t : ℝ ↦ A (p + t • h) h) :=
      (hA.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    have heval (t : ℝ) : ev (A (p + t • h) h) = (A (p + t • h) h).val.toFun x := hev _
    have hpointint : IntervalIntegrable
        (fun t : ℝ ↦ (A (p + t • h) h).val.toFun x) volume 0 1 := by
      simpa only [Function.comp_def, heval] using
        (ev.continuous.comp hcont).intervalIntegrable (μ := volume) 0 1
    calc
      _ = ev (∫ t : ℝ in 0..1, A (p + t • h) h) := (hev _).symm
      _ = ∫ t : ℝ in 0..1, (A (p + t • h) h).val.toFun x := by
        rw [← ev.intervalIntegral_comp_comm (hint p h)]
        simp only [heval]
      _ = (F (p + h)).val.toFun x - (F p).val.toFun x := by
        simpa only [one_smul, zero_smul, add_zero] using
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hpoint p h x t) hpointint
      _ = ev (F (p + h) - F p) := by rw [ev.map_sub, hev, hev]
      _ = _ := hev _
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨A, hA, ?_⟩
  intro p
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ :=
    (Metric.continuousAt_iff (f := A) (a := p)).mp hA.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds p hδ] with q hq
  let h := q - p
  have hqp : p + h = q := by dsimp [h]; abel
  have hh0 : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hq
  have hnormpoint (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖(A (p + t • h) - A p) h‖ ≤ ε * ‖h‖ := by
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
    have hnorm : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht'.1.le]
      exact (mul_le_mul_of_nonneg_right ht'.2 (norm_nonneg h)).trans_eq (one_mul _)
    have hsmall : dist (p + t • h) p < δ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hnorm.trans_lt hh0
    have hop : ‖A (p + t • h) - A p‖ ≤ ε := by
      rw [← dist_eq_norm (A (p + t • h)) (A p)]
      exact (hδbound hsmall).le
    exact ((A (p + t • h) - A p).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
  have hremainder : (∫ t : ℝ in 0..1, (A (p + t • h) - A p) h) =
      F q - F p - A p h := by
    change (∫ t : ℝ in 0..1, A (p + t • h) h - A p h) = _
    rw [intervalIntegral.integral_sub (hint p h) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    rw [hsegment, hqp]
  change ‖F q - F p - A p h‖ ≤ ε * ‖h‖
  rw [← hremainder]
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hnormpoint

#print axioms littlePeriodicCAlpha_contDiff_one_of_pointwise

end GlobalEmbedding.Paper
