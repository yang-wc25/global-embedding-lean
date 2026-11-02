import Smoothing.WeightedActualInverse
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Actual inverse-chart jets with the correct slow positive-order weights

The native identity D(a.symm) = (Da)⁻¹ composed with a.symm is differentiated.
First the inverse operator field is bounded from the original forward jets;
then the actual inverse chart is bounded recursively. Rescaling preserves the
positive-order weight ell^(k-1), including all parameter directions.
-/

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def actualInverseChartMajorant (B : ℝ) : ℕ → ℝ
  | 0 => 1+B
  | n+1 => actualInverseChartMajorant B n +
      ((n+1).factorial : ℝ)*B*(actualInverseChartMajorant B n)^(n+1)

theorem actualInverseChartMajorant_one_le {B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    1 ≤ actualInverseChartMajorant B n := by
  induction n with
  | zero => simp only [actualInverseChartMajorant]; linarith
  | succ n hn =>
    simp only [actualInverseChartMajorant]
    exact hn.trans (le_add_of_nonneg_right (by positivity))

private theorem actual_derivative_equation_positive_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → E) (H : E → E →L[ℝ] E) (V U : Set E)
    (hV : IsOpen V) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G V) (hH : ContDiffOn ℝ ∞ H U)
    (hmap : MapsTo G V U) (hDG : EqOn (fderiv ℝ G) (H ∘ G) V)
    (j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hHjet : ∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i H x‖ ≤ B) :
    ∀ n ≤ j, ∀ k, 1 ≤ k → k ≤ n+1 → ∀ y ∈ V,
      ‖iteratedFDeriv ℝ k G y‖ ≤ actualInverseChartMajorant B n := by
  intro n
  induction n with
  | zero =>
    intro _ k hk hk1 y hy
    have hk0 : k = 1 := by omega
    subst k
    rw [norm_iteratedFDeriv_one,hDG hy]
    have hb := hHjet 0 (by omega) (G y) (hmap hy)
    rw [norm_iteratedFDeriv_zero] at hb
    exact hb.trans (by simp only [actualInverseChartMajorant]; linarith)
  | succ n hn =>
    intro hnj k hk hkn y hy
    have hR1 := actualInverseChartMajorant_one_le hB n
    have hRstep : actualInverseChartMajorant B n ≤ actualInverseChartMajorant B (n+1) := by
      simp only [actualInverseChartMajorant]
      exact le_add_of_nonneg_right (by positivity)
    by_cases hlow : k ≤ n+1
    · exact (hn (by omega) k hk hlow y hy).trans hRstep
    have hkeq : k = (n+1)+1 := by omega
    subst k
    rw [← norm_iteratedFDeriv_fderiv]
    have heq : fderiv ℝ G =ᶠ[𝓝 y] H ∘ G :=
      Filter.EventuallyEq.filter_mono (hDG.eventuallyEq_of_mem (hV.mem_nhds hy)) le_rfl
    rw [(heq.iteratedFDeriv ℝ (n+1)).eq_of_nhds]
    have hcomp := norm_iteratedFDerivWithin_comp_le hH hG (n := n+1) (by simp)
      hU.uniqueDiffOn hV.uniqueDiffOn hmap hy
      (fun i hi => by
        rw [iteratedFDerivWithin_of_isOpen i hU (hmap hy)]
        exact hHjet i (by omega) (G y) (hmap hy))
      (fun i hi hin => by
        rw [iteratedFDerivWithin_of_isOpen i hV hy]
        exact (hn (by omega) i hi hin y hy).trans (le_self_pow₀ hR1 (by omega)))
    rw [iteratedFDerivWithin_of_isOpen (n+1) hV hy] at hcomp
    exact hcomp.trans (by
      simp only [actualInverseChartMajorant]
      linarith [zero_le_one.trans hR1])

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem actual_inverse_chart_fderiv
    (a : OpenPartialHomeomorph E E) (ha : ContDiffOn ℝ ∞ a a.source)
    (hinv : ∀ x ∈ a.source, (fderiv ℝ a x).IsInvertible) (y : E) (hy : y ∈ a.target) :
    fderiv ℝ a.symm y = (fderiv ℝ a (a.symm y)).inverse := by
  obtain ⟨L,hL⟩ := hinv (a.symm y) (a.map_target hy)
  have hd := ((ha.contDiffAt (a.open_source.mem_nhds (a.map_target hy))).differentiableAt
    (by simp)).hasFDerivAt
  rw [← hL] at hd
  rw [(a.hasFDerivAt_symm hy hd).fderiv,← hL,ContinuousLinearMap.inverse_equiv]

/-- Original forward derivatives and the inverse value reserve produce every
positive-order inverse-chart jet. No inverse higher derivative is a premise. -/
theorem actual_inverse_chart_slow_positive_jets
    (a : OpenPartialHomeomorph E E) (ha : ContDiffOn ℝ ∞ a a.source)
    (hinv : ∀ x ∈ a.source, (fderiv ℝ a x).IsInvertible)
    (j : ℕ) (ell b M : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hbase : ∀ x ∈ a.source, ‖(fderiv ℝ a x).inverse‖ ≤ b)
    (hforward : ∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ a.source,
      ell^i * ‖iteratedFDeriv ℝ (i+1) a x‖ ≤ M) :
    ContDiffOn ℝ ∞ a.symm a.target ∧
    ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
      ell^(k-1) * ‖iteratedFDeriv ℝ k a.symm y‖ ≤
        actualInverseChartMajorant (slowInverseMajorant b M j) j := by
  let P := fderiv ℝ a
  let H : E → E →L[ℝ] E := fun x => (P x).inverse
  have hP : ContDiffOn ℝ ∞ P a.source := ha.fderiv_of_isOpen a.open_source (m := ∞) (by simp)
  have hH : ContDiffOn ℝ ∞ H a.source := by
    intro x hx
    exact (((hinv x hx).contDiffAt_map_inverse).comp x
      (hP.contDiffAt (a.open_source.mem_nhds hx))).contDiffWithinAt
  have hunit : ∀ x ∈ a.source, IsUnit (P x) := fun x hx =>
    (P x).isUnit_iff_bijective.mpr (hinv x hx).bijective
  have hvalues : ∀ x ∈ a.source, ‖Ring.inverse (P x)‖ ≤ b := by
    simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using hbase
  have hPjet : ∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ a.source,
      ell^i * ‖iteratedFDeriv ℝ i P x‖ ≤ M := by
    intro i hi hij x hx
    rw [norm_iteratedFDeriv_fderiv]
    exact hforward i hi hij x hx
  have hbound := actual_inverse_slow_weighted_jets j a.source a.open_source P hP hunit
    ell b M hell hb hM hvalues hPjet
  have hHjet : ∀ i ≤ j, ∀ x ∈ a.source,
      ell^i * ‖iteratedFDeriv ℝ i H x‖ ≤ slowInverseMajorant b M j := by
    simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using hbound j le_rfl
  have his : ContDiffOn ℝ ∞ a.symm a.target := by
    intro y hy
    obtain ⟨L,hL⟩ := hinv (a.symm y) (a.map_target hy)
    have hd := ((ha.contDiffAt (a.open_source.mem_nhds (a.map_target hy))).differentiableAt
      (by simp)).hasFDerivAt
    rw [← hL] at hd
    exact (a.contDiffAt_symm hy hd (ha.contDiffAt
      (a.open_source.mem_nhds (a.map_target hy)))).contDiffWithinAt
  let e := slowDilation (D := E) ell hell.ne'
  let U := e ⁻¹' a.source
  let V := e ⁻¹' a.target
  let Q := H ∘ e
  let G : E → E := fun y => ell⁻¹ • a.symm (e y)
  have hU : IsOpen U := a.open_source.preimage e.continuous
  have hV : IsOpen V := a.open_target.preimage e.continuous
  have hQ : ContDiffOn ℝ ∞ Q U := hH.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have hpre : ContDiffOn ℝ ∞ (a.symm ∘ e) V :=
    his.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have hG : ContDiffOn ℝ ∞ G V := hpre.const_smul ell⁻¹
  have hGscale (y : E) : e (G y) = a.symm (e y) := by
    change ell • (ell⁻¹ • a.symm (e y)) = _
    exact smul_inv_smul₀ hell.ne' _
  have hmap : MapsTo G V U := by
    intro y hy
    change e (G y) ∈ a.source
    rw [hGscale]
    exact a.map_target hy
  have hQjet : ∀ i ≤ j, ∀ y ∈ U, ‖iteratedFDeriv ℝ i Q y‖ ≤ slowInverseMajorant b M j := by
    intro i hij y hy
    rw [norm_iteratedFDeriv_slowDilation H ell hell i y]
    exact hHjet i hij (e y) hy
  have hDG : EqOn (fderiv ℝ G) (Q ∘ G) V := by
    intro y hy
    have hi := ((his.contDiffAt (a.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    rw [actual_inverse_chart_fderiv a ha hinv (e y) hy] at hi
    have hd := (hi.comp y e.hasFDerivAt).const_smul ell⁻¹
    have heq : ell⁻¹ • ((fderiv ℝ a (a.symm (e y))).inverse.comp (e : E →L[ℝ] E)) =
        (fderiv ℝ a (a.symm (e y))).inverse := by
      ext v
      change ell⁻¹ • ((fderiv ℝ a (a.symm (e y))).inverse (ell • v)) = _
      rw [map_smul,inv_smul_smul₀ hell.ne']
    rw [heq] at hd
    change fderiv ℝ G y = H (e (G y))
    rw [hGscale]
    exact hd.fderiv
  have hrec := actual_derivative_equation_positive_jets G Q V U hV hU hG hQ hmap hDG
    j (slowInverseMajorant b M j) (slowInverseMajorant_nonneg hb hM j) hQjet j le_rfl
  refine ⟨his,?_⟩
  intro k hk hkj y hy
  have hy' : e.symm y ∈ V := by change e (e.symm y) ∈ a.target; simpa using hy
  have hn := hrec k hk hkj (e.symm y) hy'
  change ‖iteratedFDeriv ℝ k (fun z => ell⁻¹ • (a.symm ∘ e) z) (e.symm y)‖ ≤ _ at hn
  rw [iteratedFDeriv_const_smul_apply' ((hpre.contDiffAt (hV.mem_nhds hy')).of_le (by simp)),
    norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hell),
    norm_iteratedFDeriv_slowDilation a.symm ell hell k (e.symm y)] at hn
  have he : ell • e.symm y = y := e.apply_symm_apply y
  rw [he] at hn
  have hpow : ell⁻¹ * ell^k = ell^(k-1) := by
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Nat.succ_sub_one,pow_succ]
    field_simp
  simpa only [← mul_assoc,hpow] using hn

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_inverse_chart_slow_positive_jets
