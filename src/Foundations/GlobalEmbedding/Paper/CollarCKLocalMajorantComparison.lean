import GlobalEmbedding.Paper.CollarCKCoefficientComparison
import GlobalEmbedding.Paper.CollarCKSpatialFormalSolution
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Actual coefficient comparison on the finite dependencies of the CK recursion

Source: Gantumur, Math580 notes2, Theorem18 coefficient majorant proof.
DAG: `collar-ck-local-majorant-comparison`. Exclusive owner W4.
These are actual local estimates and the coefficient comparison induction. The full analytic
majorant theorem separately constructs its RHS bound and actual majorant Taylor equation.
-/
noncomputable section
open scoped BigOperators
namespace GlobalEmbedding.Paper

variable {Idx : Type*}

/-- Existing native lower-set truncation turns local coefficient bounds into global bounds.
No new truncation or formal PDE carrier is introduced. -/
theorem collarCKCoeffDominated_truncFinset
    (s : Finset (Idx →₀ ℕ)) (f F : MvPowerSeries Idx ℝ)
    (h : ∀ d ∈ s, |MvPowerSeries.coeff d f| ≤ MvPowerSeries.coeff d F) :
    CollarCKCoeffDominated (MvPowerSeries.truncFinset ℝ s f : MvPowerSeries Idx ℝ)
      (MvPowerSeries.truncFinset ℝ s F : MvPowerSeries Idx ℝ) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncFinset]
  by_cases hd : d ∈ s
  · simpa only [ite_eq_left hd] using h d hd
  · simp [hd]

/-- Multiplication uses only coefficients in the same finite lower set. Reuse native truncated
product coefficient preservation and the already proved global comparison. -/
theorem collarCKCoeffDominated_mul_lowerSet
    (s : Finset (Idx →₀ ℕ)) (hs : IsLowerSet (s : Set (Idx →₀ ℕ)))
    (f F g G : MvPowerSeries Idx ℝ)
    (hf : ∀ d ∈ s, |MvPowerSeries.coeff d f| ≤ MvPowerSeries.coeff d F)
    (hg : ∀ d ∈ s, |MvPowerSeries.coeff d g| ≤ MvPowerSeries.coeff d G)
    (d : Idx →₀ ℕ) (hd : d ∈ s) :
    |MvPowerSeries.coeff d (f * g)| ≤ MvPowerSeries.coeff d (F * G) := by
  have hh := ((collarCKCoeffDominated_truncFinset s f F hf).mul
    (collarCKCoeffDominated_truncFinset s g G hg)) d
  rw [← MvPolynomial.coe_mul, ← MvPolynomial.coe_mul,
    MvPolynomial.coeff_coe, MvPolynomial.coeff_coe,
    MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs f g hd,
    MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs F G hd] at hh
  exact hh

/-- Powers on a finite lower set reuse native truncation of powers; the exponent-zero case
is the actual unit series, so no zero-dimensional or constant term is omitted. -/
theorem collarCKCoeffDominated_pow_lowerSet
    (s : Finset (Idx →₀ ℕ)) (hs : IsLowerSet (s : Set (Idx →₀ ℕ)))
    (f F : MvPowerSeries Idx ℝ)
    (hf : ∀ d ∈ s, |MvPowerSeries.coeff d f| ≤ MvPowerSeries.coeff d F)
    (k : ℕ) (d : Idx →₀ ℕ) (hd : d ∈ s) :
    |MvPowerSeries.coeff d (f ^ k)| ≤ MvPowerSeries.coeff d (F ^ k) := by
  by_cases hk : k = 0
  · simpa only [hk, pow_zero] using (CollarCKCoeffDominated.one (Idx := Idx) d)
  have hpow (a : MvPowerSeries Idx ℝ) :
      MvPowerSeries.coeff d ((MvPowerSeries.truncFinset ℝ s a : MvPowerSeries Idx ℝ) ^ k) =
        MvPowerSeries.coeff d (a ^ k) := by
    have hh := congrArg (fun p : MvPolynomial Idx ℝ ↦ p.coeff d)
      (MvPowerSeries.truncFinset_truncFinset_pow hs (Nat.one_le_iff_ne_zero.mpr hk) a)
    simpa only [MvPowerSeries.coeff_truncFinset_of_mem _ hd] using hh
  have hh := ((collarCKCoeffDominated_truncFinset s f F hf).pow k) d
  rw [hpow f, hpow F] at hh
  exact hh

/-- A finite product needs only the actual coefficients in the same lower set. -/
theorem collarCKCoeffDominated_prod_lowerSet {J : Type*}
    (s : Finset (Idx →₀ ℕ)) (hs : IsLowerSet (s : Set (Idx →₀ ℕ)))
    (t : Finset J) (a A : J → MvPowerSeries Idx ℝ)
    (h : ∀ j ∈ t, ∀ d ∈ s, |MvPowerSeries.coeff d (a j)| ≤ MvPowerSeries.coeff d (A j)) :
    ∀ d ∈ s, |MvPowerSeries.coeff d (∏ j ∈ t, a j)| ≤
      MvPowerSeries.coeff d (∏ j ∈ t, A j) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro d _
    simpa using (CollarCKCoeffDominated.one (Idx := Idx) d)
  | @insert j t hj ih =>
    intro d hd
    simp only [Finset.prod_insert hj]
    exact collarCKCoeffDominated_mul_lowerSet s hs _ _ _ _
      (h j (by simp)) (ih (fun i hi ↦ h i (by simp [hi]))) d hd

/-- The coefficient of lawful nonlinear substitution needs domination only on a finite lower
set containing that coefficient. This is the local estimate needed for the genuine CK
induction; it does not assume global domination of the unknown solution. Native finite
supports justify both sums, and native lower-set truncation handles each product. -/
theorem collarCKCoeffDominated_subst_lowerSet {Src : Type*}
    (s : Finset (Idx →₀ ℕ)) (hs : IsLowerSet (s : Set (Idx →₀ ℕ)))
    (f F : MvPowerSeries Src ℝ) (hf : CollarCKCoeffDominated f F)
    (a A : Src → MvPowerSeries Idx ℝ)
    (ha : MvPowerSeries.HasSubst a) (hA : MvPowerSeries.HasSubst A)
    (h : ∀ i, ∀ d ∈ s, |MvPowerSeries.coeff d (a i)| ≤ MvPowerSeries.coeff d (A i))
    (e : Idx →₀ ℕ) (he : e ∈ s) :
    |MvPowerSeries.coeff e (MvPowerSeries.subst a f)| ≤
      MvPowerSeries.coeff e (MvPowerSeries.subst A F) := by
  classical
  have hprod (d : Src →₀ ℕ) :
      |MvPowerSeries.coeff e (d.prod fun i k ↦ a i ^ k)| ≤
        MvPowerSeries.coeff e (d.prod fun i k ↦ A i ^ k) := by
    exact collarCKCoeffDominated_prod_lowerSet s hs d.support _ _
      (fun i _ b hb ↦ collarCKCoeffDominated_pow_lowerSet s hs _ _ (h i) (d i) b hb) e he
  let u (d : Src →₀ ℕ) :=
    MvPowerSeries.coeff d f * MvPowerSeries.coeff e (d.prod fun i k ↦ a i ^ k)
  let v (d : Src →₀ ℕ) :=
    MvPowerSeries.coeff d F * MvPowerSeries.coeff e (d.prod fun i k ↦ A i ^ k)
  have hu : u.HasFiniteSupport := MvPowerSeries.coeff_subst_finite ha f e
  have hv : v.HasFiniteSupport := MvPowerSeries.coeff_subst_finite hA F e
  let t := (hu.union hv).toFinset
  have hut : Function.support u ⊆ (t : Set (Src →₀ ℕ)) := by
    intro d hd
    exact (hu.union hv).mem_toFinset.mpr (Or.inl hd)
  have hvt : Function.support v ⊆ (t : Set (Src →₀ ℕ)) := by
    intro d hd
    exact (hu.union hv).mem_toFinset.mpr (Or.inr hd)
  rw [MvPowerSeries.coeff_subst ha, MvPowerSeries.coeff_subst hA]
  change |finsum u| ≤ finsum v
  rw [finsum_eq_finsetSum_of_support_subset u hut, finsum_eq_finsetSum_of_support_subset v hvt]
  calc
    |∑ d ∈ t, u d| ≤ ∑ d ∈ t, |u d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ t, v d := by
      apply Finset.sum_le_sum
      intro d _
      dsimp only [u, v]
      rw [abs_mul]
      exact mul_le_mul (hf d) (hprod d) (abs_nonneg _) (hf.nonneg _)

/-- A spatial derivative coefficient needed by a normal recursion step precedes the target in
(total degree, normal degree). Its total degree can be equal, but then its normal degree is
strictly smaller. This is the actual ordering, rather than a false total-degree decrease. -/
theorem collarCK_spatial_coefficient_precedes {n : ℕ}
    (d e : CollarCKFullIndex n →₀ ℕ) (hde : d ≤ e) (i : Fin n) :
    (d + Finsupp.single (Sum.inr i) 1).degree <
        (e + Finsupp.single (Sum.inl ()) 1).degree ∨
      ((d + Finsupp.single (Sum.inr i) 1).degree =
          (e + Finsupp.single (Sum.inl ()) 1).degree ∧
        (d + Finsupp.single (Sum.inr i) 1 : CollarCKFullIndex n →₀ ℕ) (Sum.inl ()) <
          (e + Finsupp.single (Sum.inl ()) 1 : CollarCKFullIndex n →₀ ℕ) (Sum.inl ())) := by
  have hdeg := Finsupp.degree_mono hde
  by_cases hlt : d.degree < e.degree
  · left
    simpa only [map_add, Finsupp.degree_single] using Nat.add_lt_add_right hlt 1
  · right
    have heq : d.degree = e.degree := le_antisymm hdeg (Nat.le_of_not_gt hlt)
    constructor
    · simp only [map_add, Finsupp.degree_single, heq]
    · simpa using Nat.lt_succ_of_le (hde (Sum.inl ()))

/-- Formal CK coefficient comparison by total degree followed by normal degree.
The hypotheses here are the actual two formal PDE identities, the initial series, nonnegative
majorant coefficients, and coefficient domination of the given RHS. They contain no desired
bound for the solution. The final analytic theorem must discharge these identities using the
same W3 formal solution, W6 Taylor packaging and the actual Goursat majorant. -/
theorem collarCK_formal_coefficient_comparison {n m : ℕ} {Src : Type*}
    (u : Fin m → MvPowerSeries (CollarCKFullIndex n) ℝ)
    (U : MvPowerSeries (CollarCKFullIndex n) ℝ)
    (H : Fin m → MvPowerSeries Src ℝ) (F : MvPowerSeries Src ℝ)
    (hH : ∀ j, CollarCKCoeffDominated (H j) F)
    (a A : Src → MvPowerSeries (CollarCKFullIndex n) ℝ)
    (ha : MvPowerSeries.HasSubst a) (hA : MvPowerSeries.HasSubst A)
    (hslots : ∀ s,
      CollarCKCoeffDominated (a s) (A s) ∨
      (∃ j, a s = u j ∧ A s = U) ∨
      (∃ i : Fin n, ∃ j, a s = MvPowerSeries.pderiv (Sum.inr i) (u j) ∧
        A s = MvPowerSeries.pderiv (Sum.inr i) U))
    (hu : ∀ j, MvPowerSeries.pderiv (Sum.inl ()) (u j) = MvPowerSeries.subst a (H j))
    (hU : MvPowerSeries.pderiv (Sum.inl ()) U = MvPowerSeries.subst A F)
    (hinit : ∀ j d, d (Sum.inl ()) = 0 → MvPowerSeries.coeff d (u j) = 0)
    (hpos : ∀ d, 0 ≤ MvPowerSeries.coeff d U) :
    ∀ j, CollarCKCoeffDominated (u j) U := by
  classical
  have hall : ∀ N k : ℕ, ∀ j (d : CollarCKFullIndex n →₀ ℕ),
      d.degree = N → d (Sum.inl ()) = k →
      |MvPowerSeries.coeff d (u j)| ≤ MvPowerSeries.coeff d U := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ihN =>
      intro k
      induction k using Nat.strong_induction_on with
      | h k ihk =>
        intro j d hdeg hk
        by_cases hk0 : k = 0
        · rw [hinit j d (by omega), abs_zero]
          exact hpos d
        have hdpos : 1 ≤ d (Sum.inl ()) := by omega
        have hsingle : Finsupp.single (Sum.inl ()) 1 ≤ d := by
          intro s
          rcases s with ⟨⟩ | i
          · simpa only [Finsupp.single_eq_same] using hdpos
          · simp
        let e := d - Finsupp.single (Sum.inl ()) 1
        have heq : e + Finsupp.single (Sum.inl ()) 1 = d := tsub_add_cancel_of_le hsingle
        have hedeg : e.degree < N := by
          have hh := congrArg Finsupp.degree heq
          simp only [map_add, Finsupp.degree_single] at hh
          omega
        have hlocal : ∀ s, ∀ b ≤ e,
            |MvPowerSeries.coeff b (a s)| ≤ MvPowerSeries.coeff b (A s) := by
          intro s b hbe
          rcases hslots s with hfixed | ⟨l, hau, hAU⟩ | ⟨i, l, had, hAD⟩
          · exact hfixed b
          · rw [hau, hAU]
            exact ihN b.degree ((Finsupp.degree_mono hbe).trans_lt hedeg)
              (b (Sum.inl ())) l b rfl rfl
          · rw [had, hAD, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
              abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b (Sum.inr i) : ℝ) + 1)]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hpre := collarCK_spatial_coefficient_precedes b e hbe i
            rw [heq] at hpre
            rcases hpre with hlt | ⟨hequal, hnormal⟩
            · exact ihN _ (by simpa only [hdeg] using hlt)
                ((b + Finsupp.single (Sum.inr i) 1 : CollarCKFullIndex n →₀ ℕ) (Sum.inl ()))
                l _ rfl rfl
            · exact ihk _ (by simpa only [hk] using hnormal) l _
                (hequal.trans hdeg) rfl
        have hs : IsLowerSet (↑(Finset.Iic e) : Set (CollarCKFullIndex n →₀ ℕ)) := by
          intro x y hxy hy
          exact Finset.mem_Iic.mpr (hxy.trans (Finset.mem_Iic.mp hy))
        have hstep := collarCKCoeffDominated_subst_lowerSet (Finset.Iic e) hs
          (H j) F (hH j) a A ha hA
          (fun s b hb ↦ hlocal s b (Finset.mem_Iic.mp hb)) e (by simp)
        rw [← hu j, ← hU, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
          heq, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e (Sum.inl ()) : ℝ) + 1)] at hstep
        exact (mul_le_mul_iff_left₀ (by positivity : 0 < (e (Sum.inl ()) : ℝ) + 1)).mp hstep
  intro j d
  exact hall d.degree (d (Sum.inl ())) j d rfl rfl

#print axioms collarCK_formal_coefficient_comparison
#print axioms collarCK_spatial_coefficient_precedes
#print axioms collarCKCoeffDominated_prod_lowerSet
#print axioms collarCKCoeffDominated_subst_lowerSet
#print axioms collarCKCoeffDominated_truncFinset
#print axioms collarCKCoeffDominated_mul_lowerSet
#print axioms collarCKCoeffDominated_pow_lowerSet

end GlobalEmbedding.Paper
