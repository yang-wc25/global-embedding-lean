import GlobalEmbedding.Paper.BalancedUniformFamilyContraction
import GlobalEmbedding.Paper.BalancedImplicitBranch
import GlobalEmbedding.Paper.BalancedImplicitNeumannBound

/-!
# Actual joint smoothness on one interval uniform in all auxiliary parameters

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 403–425.
DAG node: `balanced-uniform-joint-smooth-branch`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Original jointly smooth uniformly small data construct a joint branch on one common interval.

For existence only, restrict the auxiliary indices to U and extend the source data by zero
outside the given time interval. Apply the actual uniform family contraction once and choose
its actual solutions, without any continuity assumption. Inside the true original domain
these are the original equations with a common linear size bound. A single uniform shrink
makes the original quadratic linearization norm at most one half for every auxiliary
parameter. On that genuine open product the original implicit theorem proves joint C∞,
strict-small uniqueness and vanishing at time0. The actual Neumann inverse bound is at most
two on the same interval. No exterior source regularity or derivative-order-dependent
interval shrink is used. Source: the common interval and all mixed orders in `lem:balanced`. -/
theorem balanced_uniform_joint_smooth_branch
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (Q : X →L[ℝ] X →L[ℝ] Y) (hQ : ∀ x y, Q x y = Q y x)
    (U : Set E) (hU : IsOpen U) (R : ℝ) (hR : 0 < R)
    (A : E × ℝ → Y →L[ℝ] X) (f : E × ℝ → X) (K : ℝ)
    (hbound : ∃ L : ℝ, ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) R, ‖A z‖ ≤ L)
    (hforcing : ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) R, ‖f z‖ ≤ K * |z.2|)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Metric.ball (0 : ℝ) R))
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ Metric.ball (0 : ℝ) R)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ δ ≤ R ∧ ∃ v : E × ℝ → X,
      ContDiffOn ℝ ∞ v (U ×ˢ Metric.ball (0 : ℝ) δ) ∧
      (∀ p ∈ U, v (p, 0) = 0) ∧
      (∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) δ,
        v z = f z + A z (Q (v z) (v z)) ∧ ‖v z‖ ≤ C * |z.2| ∧
          ‖(2 : ℝ) • (A z).comp (Q (v z))‖ ≤ 1 / 2 ∧
          (ContinuousLinearMap.id ℝ X - (2 : ℝ) • (A z).comp (Q (v z))).IsInvertible ∧
          ‖(ContinuousLinearMap.id ℝ X - (2 : ℝ) • (A z).comp (Q (v z))).inverse‖ ≤ 2) ∧
      ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) δ, ∀ w : X,
        w = f z + A z (Q w w) → ‖(2 : ℝ) • (A z).comp (Q w)‖ < 1 → w = v z := by
  classical
  obtain ⟨L, hL⟩ := hbound
  have htime {t : ℝ} (ht : |t| < R) : t ∈ Metric.ball (0 : ℝ) R := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  have hAb (p : U) (t : ℝ) (ht : |t| < R) : ‖A (p.val, t)‖ ≤ |L| + 1 :=
    (hL (p.val, t) ⟨p.property, htime ht⟩).trans
      ((le_abs_self L).trans (le_add_of_nonneg_right (by norm_num)))
  let Kpos := max K 0
  have hKpos : 0 ≤ Kpos := le_max_right _ _
  let ae : U → ℝ → Y →L[ℝ] X := fun p t ↦ if |t| < R then A (p.val, t) else 0
  let fe : U → ℝ → X := fun p t ↦ if |t| < R then f (p.val, t) else 0
  have hae (p : U) (t : ℝ) : ‖ae p t‖ ≤ |L| + 1 := by
    dsimp only [ae]
    split_ifs with ht
    · exact hAb p t ht
    · simp only [norm_zero]
      positivity
  have hfe (p : U) (t : ℝ) : ‖fe p t‖ ≤ Kpos * |t| := by
    dsimp only [fe]
    split_ifs with ht
    · exact (hforcing (p.val, t) ⟨p.property, htime ht⟩).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg t))
    · simp only [norm_zero]
      exact mul_nonneg hKpos (abs_nonneg t)
  obtain ⟨r, δ₀, C, hr, hδ₀, hC, hsol⟩ :=
    uniform_quadratic_family_contraction Q ae fe Kpos ⟨|L| + 1, hae⟩ hfe
  let v : E × ℝ → X := fun z ↦ if hp : z.1 ∈ U then
    if ht : |z.2| < δ₀ then (hsol z.2 ht).choose ⟨z.1, hp⟩ else 0 else 0
  have hv (z : E × ℝ) (hp : z.1 ∈ U) (ht : |z.2| < δ₀) (htR : |z.2| < R) :
      v z = f z + A z (Q (v z) (v z)) ∧ ‖v z‖ ≤ C * |z.2| := by
    have h := (hsol z.2 ht).choose_spec.1 ⟨z.1, hp⟩
    have hvalue : v z = (hsol z.2 ht).choose ⟨z.1, hp⟩ := by
      simp only [v, dite_eq_left hp, dite_eq_left ht]
    rw [hvalue]
    simpa only [ae, fe, ite_eq_left htR] using And.intro h.2.1 h.2.2
  let D := 2 * (|L| + 1) * (‖Q‖ + 1) * (C + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  let η := 1 / (2 * D)
  have hη : 0 < η := by dsimp [η]; positivity
  have hDη : D * η = 1 / 2 := by dsimp [η]; field_simp
  let δ := min δ₀ (min R η)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hR hη)
  have hparts (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) δ) :
      |t| < δ₀ ∧ |t| < R ∧ |t| < η := by
    have htδ : |t| < δ := by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
    exact ⟨htδ.trans_le (min_le_left _ _),
      htδ.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      htδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hsubset : U ×ˢ Metric.ball (0 : ℝ) δ ⊆ U ×ˢ Metric.ball (0 : ℝ) R :=
    fun z hz ↦ ⟨hz.1, htime (hparts z.2 hz.2).2.1⟩
  have hsmall (z : E × ℝ) (hz : z ∈ U ×ˢ Metric.ball (0 : ℝ) δ) :
      ‖(2 : ℝ) • (A z).comp (Q (v z))‖ ≤ 1 / 2 := by
    have hAt : ‖A z‖ ≤ |L| + 1 := hAb ⟨z.1, hz.1⟩ z.2 (hparts z.2 hz.2).2.1
    have hvsize : ‖v z‖ ≤ (C + 1) * |z.2| :=
      (hv z hz.1 (hparts z.2 hz.2).1 (hparts z.2 hz.2).2.1).2.trans
        (by nlinarith [abs_nonneg z.2])
    calc
      ‖(2 : ℝ) • (A z).comp (Q (v z))‖ = 2 * ‖(A z).comp (Q (v z))‖ := by
        rw [norm_smul, Real.norm_ofNat]
      _ ≤ 2 * (‖A z‖ * ‖Q (v z)‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * ((|L| + 1) * ((‖Q‖ + 1) * ((C + 1) * |z.2|))) := by
        gcongr
        exact (Q.le_opNorm (v z)).trans
          (mul_le_mul (by linarith) hvsize (norm_nonneg _) (by positivity))
      _ = D * |z.2| := by dsimp [D]; ring
      _ ≤ D * η := mul_le_mul_of_nonneg_left (hparts z.2 hz.2).2.2.le hD.le
      _ = 1 / 2 := hDη
  have hstrict : ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) δ,
      ‖(2 : ℝ) • (A z).comp (Q (v z))‖ < 1 :=
    fun z hz ↦ (hsmall z hz).trans_lt (by norm_num)
  have hfixed : ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) δ,
      v z = f z + A z (Q (v z) (v z)) :=
    fun z hz ↦ (hv z hz.1 (hparts z.2 hz.2).1 (hparts z.2 hz.2).2.1).1
  have hsmooth := balanced_fixed_implicit_branch (U ×ˢ Metric.ball (0 : ℝ) δ)
    (hU.prod Metric.isOpen_ball) Q hQ f A v (hf.mono hsubset) (hA.mono hsubset) hfixed hstrict
  refine ⟨δ, C, hδ, hC, (min_le_right _ _).trans (min_le_left _ _),
    v, hsmooth.1, ?_, ?_, hsmooth.2⟩
  · intro p hp
    have h := (hv (p, 0) hp (by simpa using hδ₀) (by simpa using hR)).2
    simp only [abs_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  · intro z hz
    have hi := balanced_implicit_neumann_uniform_bound
      ((2 : ℝ) • (A z).comp (Q (v z))) (hsmall z hz) (by norm_num)
    refine ⟨hfixed z hz, (hv z hz.1 (hparts z.2 hz.2).1 (hparts z.2 hz.2).2.1).2,
      hsmall z hz, hi.1, ?_⟩
    convert hi.2 using 1
    norm_num

#print axioms balanced_uniform_joint_smooth_branch

end GlobalEmbedding.Paper
