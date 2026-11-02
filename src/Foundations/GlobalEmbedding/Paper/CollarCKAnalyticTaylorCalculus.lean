import GlobalEmbedding.Paper.CollarCKTaylorCoordinatePartial
import GlobalEmbedding.Paper.CollarCKTaylorComposition
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Actual analytic calculus of the shared commutative Taylor coefficients

Source: Gantumur, notes2, Theorem 18, coefficient differentiation and rational identities.
All coefficients use the accepted `collarCKTaylorCoeff` word fibers without rescaling.
The scalar formal package is the literal function `d ↦ collarCKTaylorCoeff p d`.
-/

namespace GlobalEmbedding.Paper

open scoped Topology
open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The actual value at the origin is exactly the native constant coefficient of the
literal shared package, including an empty coordinate type. -/
theorem collarCKTaylorPackage_constantCoeff (f : (σ → ℝ) → ℝ)
    (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (hp : HasFPowerSeriesAt f p 0) :
    constantCoeff (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries σ ℝ) = f 0 := by
  change collarCKTaylorCoeff p 0 = f 0
  have he := collarCKTaylorHomogeneous_eval p 0 (0 : σ → ℝ)
  rw [MvPolynomial.eval_zero] at he
  have hc := collarCKTaylorHomogeneous_coeff p 0 0
  simp only [map_zero, ite_true] at hc
  exact hc.symm.trans (he.trans (hp.coeff_zero _))

/-- A genuine constant multilinear expansion has exactly the native constant formal
series under the unchanged shared word-fiber coefficients. -/
theorem collarCKTaylorPackage_const (c : ℝ) :
    (fun d ↦ collarCKTaylorCoeff (constFormalMultilinearSeries ℝ (σ → ℝ) c) d :
      MvPowerSeries σ ℝ) = C c := by
  apply MvPowerSeries.ext
  intro d
  by_cases hd : d = 0
  · subst d
    exact collarCKTaylorPackage_constantCoeff (fun _ : σ → ℝ ↦ c) _
      hasFPowerSeriesAt_const
  · have hdeg : d.degree ≠ 0 := fun h ↦ hd ((Finsupp.degree_eq_zero_iff d).mp h)
    change collarCKTaylorCoeff (constFormalMultilinearSeries ℝ (σ → ℝ) c) d = _
    simp only [collarCKTaylorCoeff, constFormalMultilinearSeries_apply_of_nonzero hdeg,
      zero_apply, Finset.sum_const_zero, coeff_C, hd, ite_false]

/-- Native bilinear Taylor expansion at an arbitrary center, in two actual coordinates,
packages as the expected quadratic polynomial. The proof uses the published homogeneous
polynomial dictionary and native finite bilinear expansion, without word enumeration. -/
theorem collarCKTaylorPackage_bilinear (a b : ℝ) :
    let L : (Bool → ℝ) →L[ℝ] ℝ × ℝ :=
      (ContinuousLinearMap.proj false).prod (ContinuousLinearMap.proj true)
    let p :=
      ((ContinuousLinearMap.mul ℝ ℝ).fpowerSeriesBilinear (a, b)).compContinuousLinearMap L
    (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries Bool ℝ) =
      (C a + X false) * (C b + X true) := by
  intro L p
  let H (k : ℕ) : MvPolynomial Bool ℝ :=
    truncFinset ℝ (Finset.univ.image (collarCKWordIndex (σ := Bool) (k := k)))
      (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries Bool ℝ)
  have hz (k : ℕ) (hk : 3 ≤ k) : p k = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hj : 3 + j = j + 3 := Nat.add_comm _ _
    rw [hj]
    ext v
    simp [p, FormalMultilinearSeries.compContinuousLinearMap]
  have hfinite (d : Bool →₀ ℕ) (hd : 3 ≤ d.degree) : collarCKTaylorCoeff p d = 0 := by
    simp only [collarCKTaylorCoeff, hz _ hd, zero_apply, Finset.sum_const_zero]
  have hc (d : Bool →₀ ℕ) :
      (∑ k ∈ Finset.range 3, H k).coeff d =
        if d.degree < 3 then collarCKTaylorCoeff p d else 0 := by
    simp only [MvPolynomial.coeff_sum]
    simp_rw [show ∀ k, (H k).coeff d =
      if d.degree = k then collarCKTaylorCoeff p d else 0 from
        fun k ↦ collarCKTaylorHomogeneous_coeff p k d]
    simp [eq_comm]
  have hpackage : (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries Bool ℝ) =
      (↑(∑ k ∈ Finset.range 3, H k : MvPolynomial Bool ℝ) : MvPowerSeries Bool ℝ) := by
    apply MvPowerSeries.ext
    intro d
    rw [MvPolynomial.coeff_coe, hc]
    change collarCKTaylorCoeff p d = _
    by_cases hd : d.degree < 3
    · exact (ite_eq_left hd).symm
    · simpa only [hd, ite_false] using hfinite d (by omega)
  have hpoly : (∑ k ∈ Finset.range 3, H k) =
      (MvPolynomial.C a + MvPolynomial.X false) *
        (MvPolynomial.C b + MvPolynomial.X true) := by
    apply MvPolynomial.funext
    intro z
    simp only [map_sum]
    simp_rw [show ∀ k, MvPolynomial.eval z (H k) = p k (fun _ ↦ z) from
      fun k ↦ collarCKTaylorHomogeneous_eval p k z]
    simp [Finset.sum_range_succ, p, FormalMultilinearSeries.compContinuousLinearMap,
      ContinuousLinearMap.fpowerSeriesBilinear, ContinuousLinearMap.deriv₂,
      L]
    ring
  rw [hpackage, hpoly]
  simp only [MvPolynomial.coe_mul, MvPolynomial.coe_add, MvPolynomial.coe_C,
    MvPolynomial.coe_X]
  rfl

/-- Raw subtraction uses the same shared fibers and the native additive structure. -/
theorem collarCKTaylorPackage_sub (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) :
    (fun d ↦ collarCKTaylorCoeff (p - q) d : MvPowerSeries σ ℝ) =
      (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries σ ℝ) -
        (fun d ↦ collarCKTaylorCoeff q d : MvPowerSeries σ ℝ) := by
  apply MvPowerSeries.ext
  intro d
  change collarCKTaylorCoeff (p - q) d =
    collarCKTaylorCoeff p d - collarCKTaylorCoeff q d
  simp only [collarCKTaylorCoeff, FormalMultilinearSeries.sub_apply,
    sub_apply, Finset.sum_sub_distrib]

/-- An actual coordinate projection of an analytic vector map has exactly the component
of the shared coefficients. Reuse the accepted raw projection dictionary. -/
theorem collarCKTaylorPackage_projection {τ : Type*} [Fintype τ] [DecidableEq τ]
    (f : (σ → ℝ) → (τ → ℝ)) (p : FormalMultilinearSeries ℝ (σ → ℝ) (τ → ℝ))
    (hp : HasFPowerSeriesAt f p 0) (i : τ)
    (q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hq : HasFPowerSeriesAt (fun z ↦ f z i) q 0) :
    (fun d ↦ collarCKTaylorCoeff q d : MvPowerSeries σ ℝ) =
      (fun d ↦ collarCKTaylorCoeff p d i : MvPowerSeries σ ℝ) := by
  obtain ⟨ρ, hball⟩ := hp
  let T : (τ → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let r := T.compFormalMultilinearSeries p
  have hr : HasFPowerSeriesAt (fun z ↦ f z i) r 0 :=
    (T.comp_hasFPowerSeriesOnBall hball).hasFPowerSeriesAt
  apply MvPowerSeries.ext
  intro d
  exact (collarCKTaylorCoeff_unique _ q r hq hr d).trans
    (collarCKTaylorCoeff_component p i d)

/-- Actual multiplication becomes native multiplication of the shared formal packages.
Use the sole published nonlinear composition dictionary with centered actual inputs and
the native bilinear expansion, so no convolution or word partition is reproved. -/
theorem collarCKTaylorPackage_mul (f g : (σ → ℝ) → ℝ)
    (p q r : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0)
    (hr : HasFPowerSeriesAt (f * g) r 0) :
    let Pp : MvPowerSeries σ ℝ := fun d ↦ collarCKTaylorCoeff p d
    let Pq : MvPowerSeries σ ℝ := fun d ↦ collarCKTaylorCoeff q d
    let Pr : MvPowerSeries σ ℝ := fun d ↦ collarCKTaylorCoeff r d
    Pr = Pp * Pq := by
  intro Pp Pq Pr
  let a := f 0
  let b := g 0
  let pc := p - constFormalMultilinearSeries ℝ (σ → ℝ) a
  let qc := q - constFormalMultilinearSeries ℝ (σ → ℝ) b
  let v : (σ → ℝ) → (Bool → ℝ) := fun z i ↦ cond i (g z - b) (f z - a)
  let s := FormalMultilinearSeries.pi (fun i : Bool ↦ cond i qc pc)
  have hpc : HasFPowerSeriesAt (fun z ↦ f z - a) pc 0 := hp.sub hasFPowerSeriesAt_const
  have hqc : HasFPowerSeriesAt (fun z ↦ g z - b) qc 0 := hq.sub hasFPowerSeriesAt_const
  have hs : HasFPowerSeriesAt v s 0 := HasFPowerSeriesAt.pi (fun i ↦ by
    cases i
    · exact hpc
    · exact hqc)
  have hv : v 0 = 0 := by ext i; cases i <;> simp [v, a, b]
  let L : (Bool → ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.proj false).prod (ContinuousLinearMap.proj true)
  let t := ((ContinuousLinearMap.mul ℝ ℝ).fpowerSeriesBilinear (a, b)).compContinuousLinearMap L
  let F : (Bool → ℝ) → ℝ := fun z ↦ (a + z false) * (b + z true)
  have ht : HasFPowerSeriesAt F t 0 := by
    have hb := ((ContinuousLinearMap.mul ℝ ℝ).hasFPowerSeriesAt_bilinear (a, b)).comp_sub
      (-(a, b))
    have hb' : HasFPowerSeriesAt (fun z : ℝ × ℝ ↦ (a + z.1) * (b + z.2))
        ((ContinuousLinearMap.mul ℝ ℝ).fpowerSeriesBilinear (a, b)) 0 := by
      simpa only [add_neg_cancel, sub_neg_eq_add, Prod.fst_add, Prod.snd_add,
        ContinuousLinearMap.mul_apply', add_comm]
        using hb
    simpa only [F, t, Function.comp_def, L, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.proj_apply, map_zero] using
      (hb'.compContinuousLinearMap (u := L) (x := 0))
  have hfun : F ∘ v = f * g := by
    funext z
    simp only [Function.comp_apply, F, v, Bool.cond_false, Bool.cond_true, Pi.mul_apply]
    ring
  have hr' : HasFPowerSeriesAt (F ∘ v) r 0 := by rw [hfun]; exact hr
  have hcomp := collarCKTaylorCoeff_analytic_comp v F t s r hs ht hr' hv
  let A : Bool → MvPowerSeries σ ℝ := fun i d ↦ collarCKTaylorCoeff
    ((ContinuousLinearMap.proj i).compFormalMultilinearSeries s) d
  change Pr = subst A _ at hcomp
  have hs0 (w) : s 0 w = 0 := (hs.coeff_zero w).trans hv
  have hsubst : HasSubst A := collarCKTaylorCoeff_components_hasSubst s hs0
  have hproj (i : Bool) : A i =
        (fun d ↦ collarCKTaylorCoeff (cond i qc pc) d : MvPowerSeries σ ℝ) := by
    apply MvPowerSeries.ext
    intro d
    change collarCKTaylorCoeff
      ((ContinuousLinearMap.proj i).compFormalMultilinearSeries s) d =
        collarCKTaylorCoeff (cond i qc pc) d
    rw [collarCKTaylorCoeff_component]
    simp only [collarCKTaylorCoeff, s, FormalMultilinearSeries.pi,
      ContinuousMultilinearMap.pi_apply, Finset.sum_apply]
  let O1 : MvPowerSeries Bool ℝ := C a + X false
  let O2 : MvPowerSeries Bool ℝ := C b + X true
  have houter : (fun d ↦ collarCKTaylorCoeff t d : MvPowerSeries Bool ℝ) = O1 * O2 :=
    collarCKTaylorPackage_bilinear a b
  have hcomp' : Pr = subst A (O1 * O2) :=
    hcomp.trans (congrArg (fun U : MvPowerSeries Bool ℝ ↦ subst A U) houter)
  rw [subst_mul hsubst] at hcomp'
  have hO1 : subst A O1 = C a + A false := by
    exact (subst_add hsubst (C a) (X false)).trans (by rw [subst_C, subst_X hsubst])
  have hO2 : subst A O2 = C b + A true := by
    exact (subst_add hsubst (C b) (X true)).trans (by rw [subst_C, subst_X hsubst])
  rw [hO1, hO2, hproj false, hproj true] at hcomp'

  simp only [Bool.cond_false, Bool.cond_true] at hcomp'
  rw [show (fun d ↦ collarCKTaylorCoeff pc d : MvPowerSeries σ ℝ) =
      Pp - C a from
    (collarCKTaylorPackage_sub p _).trans (by rw [collarCKTaylorPackage_const]; rfl),
    show (fun d ↦ collarCKTaylorCoeff qc d : MvPowerSeries σ ℝ) =
      Pq - C b from
    (collarCKTaylorPackage_sub q _).trans (by rw [collarCKTaylorPackage_const]; rfl)] at hcomp'
  have ha : C a + (Pp - C a) = Pp := by abel
  have hb : C b + (Pq - C b) = Pq := by abel
  exact hcomp'.trans (congrArg₂ (fun x y : MvPowerSeries σ ℝ ↦ x * y) ha hb)

/-- Any genuine expansion of a constant function has the native constant formal package;
no particular nonsymmetric expansion witness is required. -/
theorem collarCKTaylorPackage_analytic_const (c : ℝ)
    (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt (fun _ ↦ c) p 0) :
    (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries σ ℝ) = C c := by
  have hs : (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries σ ℝ) =
      (fun d ↦ collarCKTaylorCoeff (constFormalMultilinearSeries ℝ (σ → ℝ) c) d :
        MvPowerSeries σ ℝ) := by
    apply MvPowerSeries.ext
    intro d
    exact collarCKTaylorCoeff_unique (fun _ ↦ c) p _ hp hasFPowerSeriesAt_const d
  exact hs.trans (collarCKTaylorPackage_const c)

/-- An actual analytic reciprocal with nonzero value at the origin becomes the native
formal inverse. Actual continuity gives a nonvanishing neighborhood; the product theorem
and native uniqueness of an inverse discharge the entire formal identity. -/
theorem collarCKTaylorPackage_inv (f : (σ → ℝ) → ℝ)
    (p q : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt f⁻¹ q 0) (hf0 : f 0 ≠ 0) :
    let P : MvPowerSeries σ ℝ := fun d ↦ collarCKTaylorCoeff p d
    let Q : MvPowerSeries σ ℝ := fun d ↦ collarCKTaylorCoeff q d
    Q = P⁻¹ := by
  intro P Q
  have hP : constantCoeff P ≠ 0 := by
    rw [collarCKTaylorPackage_constantCoeff f p hp]
    exact hf0
  apply (MvPowerSeries.eq_inv_iff_mul_eq_one hP).mpr
  have hprod : HasFPowerSeriesAt (f⁻¹ * f)
      (constFormalMultilinearSeries ℝ (σ → ℝ) 1) 0 := by
    apply hasFPowerSeriesAt_const.congr
    filter_upwards [hp.analyticAt.continuousAt.eventually_ne hf0] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, inv_mul_cancel₀ hz]
  have hm : (C 1 : MvPowerSeries σ ℝ) = Q * P :=
    (collarCKTaylorPackage_const 1).symm.trans
      (collarCKTaylorPackage_mul f⁻¹ f q p _ hq hp hprod)
  exact hm.symm.trans (map_one C)

end GlobalEmbedding.Paper
