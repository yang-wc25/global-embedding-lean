import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Order.Compact

open scoped Topology ContDiff NNReal
open Filter Set WithLp

/-!
# Actual maximum principle for the period-one shifted Laplacian

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines382–386.
All spaces, derivatives, periodic translations and norms below are actual Mathlib objects.
-/

namespace GlobalEmbedding.Paper

private theorem secondDerivative_nonpos_at_global_max {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hmax : ∀ x, f x ≤ f 0) : deriv (deriv f) 0 ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) 0 := lt_of_not_ge h
  have hdf : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hcont : Continuous (deriv (deriv f)) := hdf.continuous_deriv_one
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.continuousAt.eventually (Ioi_mem_nhds hpos))
  have hsc : StrictConvexOn ℝ (Ioo (-r) r) f :=
    strictConvexOn_of_deriv2_pos (convex_Ioo _ _) hf.continuous.continuousOn
      (by
        intro x hx
        have hx' : x ∈ Ioo (-r) r := interior_subset hx
        exact hball x (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
          abs_lt, mem_Ioo] using hx'))
  have hleft : -r / 2 ∈ Ioo (-r) r := by constructor <;> linarith
  have hright : r / 2 ∈ Ioo (-r) r := by constructor <;> linarith
  have hh := hsc.2 hleft hright (by linarith : -r / 2 ≠ r / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (-r / 2) + (1 / 2 : ℝ) • (r / 2) = 0 := by
    simp only [smul_eq_mul]
    ring
  rw [hmid] at hh
  simp only [smul_eq_mul] at hh
  linarith [hmax (-r / 2), hmax (r / 2)]

private theorem hessian_nonpos_at_global_max
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x e : E)
    (hmax : ∀ y, u y ≤ u x) :
    iteratedFDeriv ℝ 2 u x (fun _ ↦ e) ≤ 0 := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ e
  let f : ℝ → ℝ := fun t ↦ u (x + L t)
  have hf : ContDiff ℝ 2 f := hu.comp (contDiff_const.add L.contDiff)
  have hfm : ∀ t, f t ≤ f 0 := by
    intro t
    simpa only [f, map_zero, add_zero] using hmax (x + L t)
  have hn := secondDerivative_nonpos_at_global_max hf hfm
  have hshift : ContDiff ℝ 2 (fun y : E ↦ u (x + y)) :=
    hu.comp (contDiff_const.add contDiff_id)
  have hc := L.iteratedFDeriv_comp_right hshift 0 (i := 2) le_rfl
  have heval := congrArg (fun p ↦ p (fun _ : Fin 2 ↦ (1 : ℝ))) hc
  have hformula : deriv (deriv f) 0 = iteratedFDeriv ℝ 2 u x (fun _ ↦ e) := by
    simpa only [Function.comp_def, ← iteratedDeriv_eq_iteratedFDeriv,
      iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, f,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero,
      iteratedFDeriv_comp_add_left, add_zero, L,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using heval
  rwa [hformula] at hn

private theorem periodic_attains_max {a : ℕ} {u : EuclideanSpace ℝ (Fin a) → ℝ}
    (hu : Continuous u)
    (hper : ∀ x (n : Fin a → ℤ), u (x + toLp 2 (fun i ↦ (n i : ℝ))) = u x) :
    ∃ x, ∀ y, u y ≤ u x := by
  let g : (Fin a → ℝ) → ℝ := fun x ↦ u (toLp 2 x)
  have hg : Continuous g := hu.comp (PiLp.continuous_toLp _ _)
  have hne : (Icc (0 : Fin a → ℝ) 1).Nonempty := ⟨0, le_rfl, by simp⟩
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hg.continuousOn
  refine ⟨toLp 2 z, ?_⟩
  intro y
  let w : Fin a → ℝ := fun i ↦ Int.fract (y i)
  have hw : w ∈ Icc (0 : Fin a → ℝ) 1 :=
    ⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩
  have hwy : toLp 2 w + toLp 2 (fun i ↦ (⌊y i⌋ : ℝ)) = y := by
    ext i
    simp [w, Int.fract_add_floor]
  have hval : u y = g w := by
    rw [← hwy, hper]
  exact hval.le.trans (hmax hw)

private theorem periodic_shifted_scalar_upper {a : ℕ}
    {u f : EuclideanSpace ℝ (Fin a) → ℝ} {B : ℝ}
    (hu : ContDiff ℝ 2 u)
    (hper : ∀ x (n : Fin a → ℤ), u (x + toLp 2 (fun i ↦ (n i : ℝ))) = u x)
    (hPDE : ∀ x, (∑ i : Fin a, iteratedFDeriv ℝ 2 u x
      (fun _ ↦ EuclideanSpace.single i 1)) - u x = f x)
    (hf : ∀ x, -B ≤ f x) : ∀ x, u x ≤ B := by
  obtain ⟨z, hz⟩ := periodic_attains_max hu.continuous hper
  have hlap : (∑ i : Fin a, iteratedFDeriv ℝ 2 u z
      (fun _ ↦ EuclideanSpace.single i 1)) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ hessian_nonpos_at_global_max hu z _ hz
  have hp := hPDE z
  have hb := hf z
  intro x
  linarith [hz x]

/-- The actual periodic shifted Laplacian has supremum contraction for real inner-product
valued C² solutions, in every spatial dimension including0 and zero target spaces.

Source: `lem:balanced`, periodic shifted Schauder inverse, lines382–386.
Proof: compactness of the actual coordinate cube and integer fractional-part reduction attain
every scalar periodic maximum. A positive second derivative at a scalar maximum would make
the function strictly convex on a small interval, contradicting its midpoint inequality;
native linear derivative composition gives the same sign for each actual directional jet.
Their finite sum is nonpositive at a maximum, so the actual shifted equation bounds each
scalar solution from above by the negative forcing lower bound. Project the given vector
solution onto its value u(x₀) using the actual inner-product continuous linear functional.
Its actual second jets commute with this functional; Cauchy–Schwarz bounds the projected
forcing by ‖u(x₀)‖B. The scalar maximum principle gives ‖u(x₀)‖²≤‖u(x₀)‖B, and cancellation
proves the result. The zero value is handled directly. No inverse or maximum principle is
assumed as a hypothesis. -/
theorem periodic_shifted_laplacian_norm_bound {a : ℕ}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u f : EuclideanSpace ℝ (Fin a) → F} {B : ℝ} (hB : 0 ≤ B)
    (hu : ContDiff ℝ 2 u)
    (hper : ∀ x (n : Fin a → ℤ), u (x + toLp 2 (fun i ↦ (n i : ℝ))) = u x)
    (hPDE : ∀ x, (∑ i : Fin a, iteratedFDeriv ℝ 2 u x
      (fun _ ↦ EuclideanSpace.single i 1)) - u x = f x)
    (hf : ∀ x, ‖f x‖ ≤ B) : ∀ x, ‖u x‖ ≤ B := by
  intro x₀
  by_cases hzero : ‖u x₀‖ = 0
  · simpa only [hzero] using hB
  have hn : 0 < ‖u x₀‖ := (norm_nonneg _).lt_of_ne' hzero
  let L : F →L[ℝ] ℝ := innerSL ℝ (u x₀)
  have hjet (x) (h : Fin 2 → EuclideanSpace ℝ (Fin a)) :
      iteratedFDeriv ℝ 2 (L ∘ u) x h = L (iteratedFDeriv ℝ 2 u x h) := by
    rw [L.iteratedFDeriv_comp_left hu.contDiffAt le_rfl]
    rfl
  have hproj : ∀ x, (∑ i : Fin a, iteratedFDeriv ℝ 2 (L ∘ u) x
      (fun _ ↦ EuclideanSpace.single i 1)) - (L ∘ u) x = (L ∘ f) x := by
    intro x
    simp only [hjet, Function.comp_apply, ← map_sum, ← map_sub, hPDE]
  have hp : ∀ x (n : Fin a → ℤ), (L ∘ u) (x + toLp 2 (fun i ↦ (n i : ℝ))) =
      (L ∘ u) x := by simp only [Function.comp_apply, hper, implies_true]
  have hforce : ∀ x, -(‖u x₀‖ * B) ≤ (L ∘ f) x := by
    intro x
    have habs : |(L ∘ f) x| ≤ ‖u x₀‖ * B :=
      (abs_real_inner_le_norm (u x₀) (f x)).trans
        (mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _))
    exact neg_le_of_abs_le habs
  have hbound := periodic_shifted_scalar_upper (L.contDiff.comp hu) hp hproj hforce x₀
  have hself : (L ∘ u) x₀ = ‖u x₀‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [hself, pow_two] at hbound
  exact (mul_le_mul_iff_right₀ hn).mp (by simpa only [mul_comm] using hbound)

/-- The actual periodic shifted resolvent preserves every supplied Hölder constant.

Source: `lem:balanced`, shifted periodic Schauder estimate, lines382–386.
Proof: for each actual shift h, the difference w(z)=u(z+h)−u(z) is genuinely C² and periodic.
Translation and subtraction commute with the actual second Frechet derivatives, so w solves
the same shifted equation with forcing f(z+h)−f(z). The supplied HolderWith bound gives the
uniform norm bound K‖h‖^α on that forcing. The proved norm maximum principle bounds w by the
same quantity. Evaluate it at the desired pair of points, then convert the actual real
distance inequality to the native HolderWith definition. This also covers exponent0 and
zero spatial/target dimensions. No lower-order norm absorption is assumed. -/
theorem periodic_shifted_laplacian_holder_contraction {a : ℕ}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u f : EuclideanSpace ℝ (Fin a) → F} {K α : ℝ≥0}
    (hu : ContDiff ℝ 2 u)
    (hper : ∀ x (n : Fin a → ℤ), u (x + toLp 2 (fun i ↦ (n i : ℝ))) = u x)
    (hPDE : ∀ x, (∑ i : Fin a, iteratedFDeriv ℝ 2 u x
      (fun _ ↦ EuclideanSpace.single i 1)) - u x = f x)
    (hf : HolderWith K α f) : HolderWith K α u := by
  intro x y
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  let h := x - y
  let w := fun z ↦ u (z + h) - u z
  have hshift : ContDiff ℝ 2 (fun z ↦ u (z + h)) :=
    hu.comp (contDiff_id.add contDiff_const)
  have hw : ContDiff ℝ 2 w := hshift.sub hu
  have hwper : ∀ z (n : Fin a → ℤ), w (z + toLp 2 (fun i ↦ (n i : ℝ))) = w z := by
    intro z n
    dsimp [w]
    rw [show z + toLp 2 (fun i ↦ (n i : ℝ)) + h =
      (z + h) + toLp 2 (fun i ↦ (n i : ℝ)) by abel, hper, hper]
  have hjet (z) (d : Fin 2 → EuclideanSpace ℝ (Fin a)) :
      iteratedFDeriv ℝ 2 w z d = iteratedFDeriv ℝ 2 u (z + h) d -
        iteratedFDeriv ℝ 2 u z d := by
    change iteratedFDeriv ℝ 2 ((fun z ↦ u (z + h)) - u) z d = _
    rw [iteratedFDeriv_sub_apply hshift.contDiffAt hu.contDiffAt]
    simp only [sub_apply, iteratedFDeriv_comp_add_right]
  have hwPDE : ∀ z, (∑ i : Fin a, iteratedFDeriv ℝ 2 w z
      (fun _ ↦ EuclideanSpace.single i 1)) - w z = f (z + h) - f z := by
    intro z
    simp only [hjet, Finset.sum_sub_distrib, w]
    rw [← hPDE (z + h), ← hPDE z]
    abel
  have hforce : ∀ z, ‖f (z + h) - f z‖ ≤ (K : ℝ) * ‖h‖ ^ (α : ℝ) := by
    intro z
    simpa only [dist_eq_norm, add_sub_cancel_left] using hf.dist_le (z + h) z
  have hb : 0 ≤ (K : ℝ) * ‖h‖ ^ (α : ℝ) := by positivity
  have hbound := periodic_shifted_laplacian_norm_bound hb hw hwper hwPDE hforce y
  have hdist : dist (u x) (u y) ≤ (K : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [w, h, add_sub_cancel, dist_eq_norm] using hbound
  exact_mod_cast hdist

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.periodic_shifted_laplacian_norm_bound
#print axioms GlobalEmbedding.Paper.periodic_shifted_laplacian_holder_contraction
