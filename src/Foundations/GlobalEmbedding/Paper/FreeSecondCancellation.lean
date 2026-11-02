import GlobalEmbedding.Paper.FreePrimitiveParameterCommutation
import GlobalEmbedding.Paper.MatrixOrbitCalculus
import GlobalEmbedding.Paper.PlanarOrbitPrimitive
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The literal scalar part of the second cancellation

Source: `literature/parallelizable-stable-plus-one/main.tex`, equation (4.7), lines 470–475.
DAG node: `free-second-cancellation`. No division by the curvature occurs.
-/

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The actual active quadratic energy, not an independently chosen function.
Source: e=|XZ|² in line 470. -/
def freeCancellationEnergy {M V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : ℝ → M → M) (Z : M → V) (x : M) : ℝ := ‖orbitDeriv R Z x‖ ^ 2

/-- The actual period average of the squared curvature, as in line 470. -/
def freeCancellationK2 {M : Type*} (R : ℝ → M → M) (κ : M → ℝ) : M → ℝ :=
  orbitAverage R (fun x ↦ κ x ^ 2)

/-- The literal b from (4.7). The denominator is an orbit average, never κ itself. -/
def freeCancellationB {M : Type*} (R : ℝ → M → M) (κ e : M → ℝ) (x : M) : ℝ :=
  κ x * orbitAverage R e x / (2 * freeCancellationK2 R κ x)

/-- The literal first weighted primitive from (4.7), with its actual integrand. -/
def freeCancellationU {M : Type*} (R : ℝ → M → M) (κ e : M → ℝ) : M → ℝ :=
  planarOrbitPrimitive R (fun x ↦ -e x / 2 + κ x * freeCancellationB R κ e x)

/-- The literal second weighted primitive from (4.7). In the geometric application
g is the genuine pairing inner(Y_i Z,XZ), and S is the actual old factor flow. -/
def freeCancellationW {M : Type*} (R S : ℝ → M → M) (κ e g : M → ℝ) : M → ℝ :=
  planarOrbitPrimitive R (fun x ↦ -g x - orbitDeriv S (freeCancellationU R κ e) x)

variable {P M : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace P M]

/-- Curvature nonzero somewhere on every actual orbit makes its squared period
average positive. Shift to such a point, use positivity of the continuous nonnegative
integrand, then use the already proved genuine average invariance to shift back.
This does not assume either a positive minimum of κ or a chosen orbit origin.
Source: k₂>0 at line 470, using the actual curvature signs in prop:matrix. -/
theorem free_cancellation_k2_pos (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (κ : M → ℝ) (hκ : Continuous κ)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0) (x : M) :
    0 < freeCancellationK2 R.flow κ x := by
  obtain ⟨s, hs⟩ := hn x
  have hc : Continuous (fun t : ℝ ↦ κ (R.flow t (R.flow s x)) ^ 2) :=
    (hκ.comp (R.smooth.continuous.comp (continuous_id.prodMk continuous_const))).pow 2
  have hp : 0 < orbitAverage R.flow (fun y ↦ κ y ^ 2) (R.flow s x) := by
    unfold orbitAverage
    apply intervalIntegral.integral_pos (by norm_num) hc.continuousOn
      (fun t _ ↦ sq_nonneg _)
    exact ⟨0, by norm_num, by simpa only [R.flow_zero] using sq_pos_of_ne_zero hs⟩
  simpa only [freeCancellationK2, matrix_orbitAverage_invariant R.flow R.flow_add R.flow_one] using hp

/-- The actual scalar b has the required mean-cancellation property. Average
invariance makes its coefficient av(e)/(2k₂) constant along the orbit. Pull the
constant through the genuine integral; the two terms cancel because k₂≠0.
Source: the first zero-mean input in (4.7), line 471. -/
theorem free_cancellation_input_average_zero (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (κ e : M → ℝ) (hκ : Continuous κ) (he : Continuous e)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0) (x : M) :
    orbitAverage R.flow (fun y ↦ -e y / 2 + κ y * freeCancellationB R.flow κ e y) x = 0 := by
  have hK := (free_cancellation_k2_pos R κ hκ hn x).ne'
  have hRc : Continuous (fun t : ℝ ↦ R.flow t x) :=
    R.smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hec := he.comp hRc
  have hκc := (hκ.comp hRc).pow 2
  have hfun : (fun t : ℝ ↦ -e (R.flow t x) / 2 +
      κ (R.flow t x) * freeCancellationB R.flow κ e (R.flow t x)) =
      fun t ↦ (-1 / 2 : ℝ) * e (R.flow t x) +
        (orbitAverage R.flow e x / (2 * freeCancellationK2 R.flow κ x)) *
          κ (R.flow t x) ^ 2 := by
    funext t
    unfold freeCancellationB freeCancellationK2
    rw [matrix_orbitAverage_invariant R.flow R.flow_add R.flow_one,
      matrix_orbitAverage_invariant R.flow R.flow_add R.flow_one]
    ring
  unfold orbitAverage
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ (-1 / 2 : ℝ) * e (R.flow t x)) volume 0 1 :=
    (continuous_const.mul hec).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ ↦
      (orbitAverage R.flow e x / (2 * freeCancellationK2 R.flow κ x)) *
        κ (R.flow t x) ^ 2) volume 0 1 :=
    (continuous_const.mul hκc).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change (-1 / 2 : ℝ) * orbitAverage R.flow e x +
    (orbitAverage R.flow e x / (2 * freeCancellationK2 R.flow κ x)) *
      freeCancellationK2 R.flow κ x = 0
  field_simp [hK]
  ring

variable [FiniteDimensional ℝ P] [IsManifold 𝓘(ℝ, P) ∞ M]

/-- The actual average on an ordinary smooth manifold is native smooth. This
generalizes the accepted single-sphere average adapter by reusing the same compact
parameter integral theorem verbatim. Source: the smooth scalar data in (4.7). -/
theorem free_orbitAverage_contMDiff (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (orbitAverage R.flow u) := by
  have hR : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) ∞
      (fun p : M × ℝ ↦ R.flow p.2 p.1) :=
    R.smooth.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hI := contMDiff_compact_parameter_integral (⊤ : ℕ∞) _ (hu.comp hR)
  apply hI.congr
  intro x
  unfold orbitAverage
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Icc_eq_integral_Ioc]
  rfl

/-- The literal b is native smooth because its actual denominator is positive
on every orbit. The positivity was proved from actual curvature nonzero, not supplied
as an extra desired analytic datum. Source: (4.7), line 471. -/
theorem freeCancellationB_contMDiff (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (κ e : M → ℝ) (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (freeCancellationB R.flow κ e) := by
  exact (hκ.mul (free_orbitAverage_contMDiff R e he)).div₀
    (contMDiff_const.mul (free_orbitAverage_contMDiff R _ (hκ.pow 2)))
    (fun x ↦ mul_ne_zero (by norm_num) (free_cancellation_k2_pos R κ hκ.continuous hn x).ne')

/-- The actual first primitive u is native smooth. Its integrand uses precisely
the literal b just proved smooth. Source: first primitive in (4.7), line 471. -/
theorem freeCancellationU_contMDiff (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (κ e : M → ℝ) (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (freeCancellationU R.flow κ e) := by
  apply planarOrbitPrimitive_contMDiff R.flow
    (R.smooth.comp (contMDiff_snd.prodMk contMDiff_fst))
  exact (he.neg.div_const 2).add (hκ.mul (freeCancellationB_contMDiff R κ e hκ he hn))

/-- The literal first primitive simultaneously has its required true active
derivative and zero actual period average. Both follow by applying the accepted
weighted primitive identities to the proved zero-mean input, not an assumed primitive.
Source: (4.7), lines 471–473. -/
theorem freeCancellationU_spec (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (κ e : M → ℝ) (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0) (x : M) :
    orbitDeriv R.flow (freeCancellationU R.flow κ e) x =
        -e x / 2 + κ x * freeCancellationB R.flow κ e x ∧
      orbitAverage R.flow (freeCancellationU R.flow κ e) x = 0 := by
  have hb := freeCancellationB_contMDiff R κ e hκ he hn
  have hh := (he.neg.div_const 2).add (hκ.mul hb)
  have hc := hh.continuous.comp
    (R.smooth.continuous.comp (continuous_id.prodMk continuous_const) :
      Continuous (fun t : ℝ ↦ R.flow t x))
  have hm := free_cancellation_input_average_zero R κ e hκ.continuous he.continuous hn x
  exact ⟨planarOrbitPrimitive_orbitDeriv_of_average_zero R.flow R.flow_zero R.flow_add
      R.flow_one _ x hc hm,
    planarOrbitPrimitive_average_zero R.flow R.flow_add R.flow_one _ x hc hm⟩

omit [FiniteDimensional ℝ P] in
/-- The energy used in (4.7) is native smooth for the actual smooth displacement Z.
Differentiate along the genuine flow using the accepted native orbit theorem, and
compose with the genuine smooth squared norm. Source: e=|XZ|² at line 470. -/
theorem freeCancellationEnergy_contMDiff {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (Z : M → V) (hZ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V) ∞ Z) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (freeCancellationEnergy R.flow Z) := by
  exact (contDiff_norm_sq ℝ).contMDiff.comp (contMDiff_orbitDeriv R.flow R.smooth Z hZ)

/-- Each literal old-indexed primitive w_i is native smooth. Its old derivative
is the actual orbit derivative of the already constructed native smooth u.
Source: second primitive in (4.7), line 471. -/
theorem freeCancellationW_contMDiff (R S : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (κ e g : M → ℝ) (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ g)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (freeCancellationW R.flow S.flow κ e g) := by
  apply planarOrbitPrimitive_contMDiff R.flow
    (R.smooth.comp (contMDiff_snd.prodMk contMDiff_fst))
  exact hg.neg.sub (contMDiff_orbitDeriv S.flow S.smooth _
    (freeCancellationU_contMDiff R κ e hκ he hn))

/-- The actual second primitive input has zero mean, and the constructed w_i has
both the exact active derivative and zero mean. The accepted W2 commutation theorem
applies to the actual smooth u with its proved mean zero, so av(Y_i u)=0. Together
with the actual mixed-period identity av(g_i)=0 this proves the displayed input mean
zero. The accepted genuine primitive identities then give both conclusions.
Source: the last zero-mean input in (4.7), lines 471–473. -/
theorem freeCancellationW_spec (R S : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (hcomm : ∀ t s x, R.flow t (S.flow s x) = S.flow s (R.flow t x))
    (κ e g : M → ℝ) (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ g)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0)
    (hmean : ∀ x, orbitAverage R.flow g x = 0) (x : M) :
    orbitAverage R.flow
        (fun y ↦ -g y - orbitDeriv S.flow (freeCancellationU R.flow κ e) y) x = 0 ∧
      orbitDeriv R.flow (freeCancellationW R.flow S.flow κ e g) x =
        -g x - orbitDeriv S.flow (freeCancellationU R.flow κ e) x ∧
      orbitAverage R.flow (freeCancellationW R.flow S.flow κ e g) x = 0 := by
  have hu := freeCancellationU_contMDiff R κ e hκ he hn
  have hYu := contMDiff_orbitDeriv S.flow S.smooth _ hu
  have hYmean := free_orbitAverage_orbitDeriv_zero R S hcomm _ hu
    (fun y ↦ (freeCancellationU_spec R κ e hκ he hn y).2) x
  have hRc : Continuous (fun t : ℝ ↦ R.flow t x) :=
    R.smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ -g (R.flow t x)) volume 0 1 :=
    ((hg.continuous.comp hRc).neg).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ ↦
      orbitDeriv S.flow (freeCancellationU R.flow κ e) (R.flow t x)) volume 0 1 :=
    (hYu.continuous.comp hRc).intervalIntegrable _ _
  have hm : orbitAverage R.flow
      (fun y ↦ -g y - orbitDeriv S.flow (freeCancellationU R.flow κ e) y) x = 0 := by
    unfold orbitAverage
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_neg]
    change -orbitAverage R.flow g x -
      orbitAverage R.flow (orbitDeriv S.flow (freeCancellationU R.flow κ e)) x = 0
    rw [hmean x, hYmean]
    ring
  have hc : Continuous (fun t : ℝ ↦
      -g (R.flow t x) - orbitDeriv S.flow (freeCancellationU R.flow κ e) (R.flow t x)) :=
    (hg.neg.sub hYu).continuous.comp hRc
  exact ⟨hm, planarOrbitPrimitive_orbitDeriv_of_average_zero R.flow R.flow_zero R.flow_add
      R.flow_one _ x hc hm,
    planarOrbitPrimitive_average_zero R.flow R.flow_add R.flow_one _ x hc hm⟩

/-- The actual scalar u,b cancel the entire active quadratic metric row, including
every curvature-zero point. Substitute its proved primitive derivative and simplify.
Source: active row 2Xu−2κb at line 473. -/
theorem freeCancellationU_active_row (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (κ e : M → ℝ) (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0) (x : M) :
    2 * orbitDeriv R.flow (freeCancellationU R.flow κ e) x -
        2 * κ x * freeCancellationB R.flow κ e x = -e x := by
  rw [(freeCancellationU_spec R κ e hκ he hn x).1]
  ring

/-- The actual w_i and u cancel the full mixed quadratic metric row. Substitute
the proved genuine primitive derivative; no mixed term is dropped.
Source: mixed row Xw_i+Y_i u at line 473. -/
theorem freeCancellationW_mixed_row (R S : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (hcomm : ∀ t s x, R.flow t (S.flow s x) = S.flow s (R.flow t x))
    (κ e g : M → ℝ) (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ g)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0)
    (hmean : ∀ x, orbitAverage R.flow g x = 0) (x : M) :
    orbitDeriv R.flow (freeCancellationW R.flow S.flow κ e g) x +
        orbitDeriv S.flow (freeCancellationU R.flow κ e) x = -g x := by
  rw [(freeCancellationW_spec R S hcomm κ e g hκ he hg hn hmean x).2.1]
  ring

#print axioms free_cancellation_k2_pos
#print axioms free_cancellation_input_average_zero
#print axioms freeCancellationU_spec
#print axioms freeCancellationEnergy_contMDiff
#print axioms freeCancellationW_spec
#print axioms freeCancellationU_active_row
#print axioms freeCancellationW_mixed_row

end GlobalEmbedding.Paper
