import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Actual independence for closed unit-speed planar profiles

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line291.
DAG node: `matrix-planar-profile-independence`.
-/

open Set Filter
open scoped Topology

namespace GlobalEmbedding.Paper

/-- An actual closed differentiable unit-speed planar profile cannot satisfy b=c·t.

Proof: the actual squared length of the source-correct PLUS shift (f+c,g) is
continuous periodic and attains a genuine global maximum. Its derivative there
is zero, so the shifted position is perpendicular to the tangent. The assumed
b=c·t makes that same shifted position parallel to the actual unit tangent.
Thus the maximum squared length is zero, so g is identically zero. At an actual
Rolle zero of f' this contradicts actual unit speed. Source: `prop:matrix`, line291. -/
private theorem no_planar_profile_parallel_shift
    (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfperiod : Function.Periodic f 1) (hgperiod : Function.Periodic g 1)
    (hunit : ∀ x, deriv f x ^ 2 + deriv g x ^ 2 = 1) (c : ℝ) :
    ¬ ∀ x, -f x * deriv g x + g x * deriv f x = c * deriv g x := by
  intro hparallel
  let Q : ℝ → ℝ := fun x ↦ (f x + c) ^ 2 + g x ^ 2
  have hQ : Continuous Q := (hf.continuous.add continuous_const).pow 2 |>.add (hg.continuous.pow 2)
  have hQperiod : Function.Periodic Q 1 := by
    intro x
    simp only [Q, hfperiod x, hgperiod x]
  obtain ⟨z, _, hzmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hQ.continuousOn
  have hglobal (x : ℝ) : Q x ≤ Q z := by
    obtain ⟨y, hy, hxy⟩ := hQperiod.exists_mem_Ico₀ (by norm_num) x
    rw [hxy]
    exact hzmax (Ico_subset_Icc_self hy)
  have hlocal : IsLocalMax Q z := Filter.Eventually.of_forall hglobal
  have hd : HasDerivAt Q
      (2 * ((f z + c) * deriv f z + g z * deriv g z)) z := by
    convert (((hf z).hasDerivAt.add_const c).pow 2).add ((hg z).hasDerivAt.pow 2) using 1; ring
  have horth : (f z + c) * deriv f z + g z * deriv g z = 0 := by
    have he := hlocal.hasDerivAt_eq_zero hd
    linarith
  have hdet : -(f z + c) * deriv g z + g z * deriv f z = 0 := by
    have he := hparallel z
    nlinarith
  have hwf : f z + c = 0 := by
    have h1 := congrArg (fun r : ℝ ↦ r * deriv f z) horth
    have h2 := congrArg (fun r : ℝ ↦ r * deriv g z) hdet
    have hu := congrArg (fun r : ℝ ↦ (f z + c) * r) (hunit z)
    nlinarith
  have hwg : g z = 0 := by
    have h1 := congrArg (fun r : ℝ ↦ r * deriv g z) horth
    have h2 := congrArg (fun r : ℝ ↦ r * deriv f z) hdet
    have hu := congrArg (fun r : ℝ ↦ g z * r) (hunit z)
    nlinarith
  have hQzero : Q z = 0 := by simp only [Q, hwf, hwg, zero_pow (by norm_num : 2 ≠ 0), zero_add]
  have hgzero : g = fun _ ↦ 0 := by
    funext x
    have hle := hglobal x
    rw [hQzero] at hle
    dsimp only [Q] at hle
    nlinarith [sq_nonneg (f x + c), sq_nonneg (g x)]
  obtain ⟨x, _, hx⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    hf.continuous.continuousOn (by simpa only [zero_add] using (hfperiod 0).symm)
  have htx : deriv g x = 0 := by rw [hgzero]; simp
  have hu := hunit x
  rw [hx, htx] at hu
  norm_num at hu

/-- Actual closed differentiable unit-speed planar profiles have nonconstant tangent
components and the two actual independent coefficient pairs required by the source.

Proof: native Rolle gives actual zeros x_f of f' and x_g of g'. Unit speed shows
f'(x_g) and g'(x_f) nonzero, so each derivative is nonconstant. Evaluate any
A+Bf'=0 at these two points to eliminate both coefficients. For At+Bb=0,
if B=0 use g'(x_f)≠0. Otherwise actual algebra gives b=(−A/B)t, contradicted
by the actual shifted maximum argument just proved. Source: `prop:matrix`, line291. -/
theorem planar_profile_independence
    (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfperiod : Function.Periodic f 1) (hgperiod : Function.Periodic g 1)
    (hunit : ∀ x, deriv f x ^ 2 + deriv g x ^ 2 = 1) :
    (∃ x y, deriv f x ≠ deriv f y) ∧
      (∃ x y, deriv g x ≠ deriv g y) ∧
      (∀ A B : ℝ, (∀ x, A + B * deriv f x = 0) → A = 0 ∧ B = 0) ∧
      (∀ A B : ℝ, (∀ x, A * deriv g x +
        B * (-f x * deriv g x + g x * deriv f x) = 0) → A = 0 ∧ B = 0) := by
  obtain ⟨xf, _, hxf⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    hf.continuous.continuousOn (by simpa only [zero_add] using (hfperiod 0).symm)
  obtain ⟨xg, _, hxg⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    hg.continuous.continuousOn (by simpa only [zero_add] using (hgperiod 0).symm)
  have hsf : deriv f xg ≠ 0 := by
    intro he
    have hu := hunit xg
    rw [he, hxg] at hu
    norm_num at hu
  have htg : deriv g xf ≠ 0 := by
    intro he
    have hu := hunit xf
    rw [hxf, he] at hu
    norm_num at hu
  refine ⟨⟨xg, xf, by simpa only [hxf] using hsf⟩,
    ⟨xf, xg, by simpa only [hxg] using htg⟩, ?_, ?_⟩
  · intro A B hrel
    have hA : A = 0 := by simpa only [hxf, mul_zero, add_zero] using hrel xf
    refine ⟨hA, ?_⟩
    have hB : B * deriv f xg = 0 := by simpa only [hA, zero_add] using hrel xg
    exact (mul_eq_zero.mp hB).resolve_right hsf
  · intro A B hrel
    by_cases hB : B = 0
    · have hA : A * deriv g xf = 0 := by simpa only [hB, zero_mul, add_zero] using hrel xf
      exact ⟨(mul_eq_zero.mp hA).resolve_right htg, hB⟩
    · exfalso
      apply no_planar_profile_parallel_shift f g hf hg hfperiod hgperiod hunit (-A / B)
      intro x
      calc
        -f x * deriv g x + g x * deriv f x = (-A * deriv g x) / B :=
          (eq_div_iff hB).mpr (by nlinarith [hrel x])
        _ = (-A / B) * deriv g x := by ring

/-- An actual global coefficient kernel for a periodic pair is also the actual
coefficient kernel after restricting both functions to the actual period interval. -/
private theorem periodic_pair_period_independent
    (p q : ℝ → ℝ) (hp : Function.Periodic p 1) (hq : Function.Periodic q 1)
    (hkernel : ∀ A B : ℝ, (∀ x, A * p x + B * q x = 0) → A = 0 ∧ B = 0) :
    LinearIndependent ℝ ![(fun t : Icc (0 : ℝ) 1 ↦ p t.val),
      (fun t : Icc (0 : ℝ) 1 ↦ q t.val)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  have hlocal (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : c 0 * p x + c 1 * q x = 0 := by
    have he := congrFun hsum ⟨x, hx⟩
    simpa only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] using he
  have hperiod : Function.Periodic (fun x ↦ c 0 * p x + c 1 * q x) 1 := by
    intro x
    dsimp only
    rw [hp x, hq x]
  have hglobal (x : ℝ) : c 0 * p x + c 1 * q x = 0 := by
    obtain ⟨y, hy, hxy⟩ := hperiod.exists_mem_Ico₀ (by norm_num) x
    rw [hxy]
    exact hlocal y (Ico_subset_Icc_self hy)
  obtain ⟨h0, h1⟩ := hkernel (c 0) (c 1) hglobal
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-- The two actual period-restricted function pairs used in the source weighted
Gram blocks are linearly independent.

Proof: use the actual coefficient independence just proved. Actual derivatives
of periodic functions are periodic, so the actual t,b pair is periodic as well.
Native periodic reduction to Ico0,1 extends any actual restricted relation to
the whole real line, where both coefficients vanish. Source: `prop:matrix`, line291. -/
theorem planar_profile_period_independence
    (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfperiod : Function.Periodic f 1) (hgperiod : Function.Periodic g 1)
    (hunit : ∀ x, deriv f x ^ 2 + deriv g x ^ 2 = 1) :
    LinearIndependent ℝ ![(fun _ : Icc (0 : ℝ) 1 ↦ (1 : ℝ)),
      (fun x : Icc (0 : ℝ) 1 ↦ deriv f x.val)] ∧
      LinearIndependent ℝ ![(fun x : Icc (0 : ℝ) 1 ↦ deriv g x.val),
        (fun x : Icc (0 : ℝ) 1 ↦ -f x.val * deriv g x.val + g x.val * deriv f x.val)] := by
  have h := planar_profile_independence f g hf hg hfperiod hgperiod hunit
  have hdf : Function.Periodic (deriv f) 1 := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun u : ℝ → ℝ ↦ deriv u x) (funext hfperiod)
  have hdg : Function.Periodic (deriv g) 1 := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun u : ℝ → ℝ ↦ deriv u x) (funext hgperiod)
  refine ⟨periodic_pair_period_independent (fun _ ↦ 1) (deriv f)
    (fun _ ↦ rfl) hdf ?_, ?_⟩
  · intro A B hrel
    apply h.2.2.1 A B
    intro x
    simpa only [mul_one] using hrel x
  · apply periodic_pair_period_independent (deriv g)
      (fun x ↦ -f x * deriv g x + g x * deriv f x) hdg ?_ h.2.2.2
    intro x
    dsimp only
    rw [hfperiod x, hgperiod x, hdf x, hdg x]

#print axioms planar_profile_independence
#print axioms planar_profile_period_independence

end GlobalEmbedding.Paper
