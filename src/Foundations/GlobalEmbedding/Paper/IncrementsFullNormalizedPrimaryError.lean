import GlobalEmbedding.Paper.IncrementsNormalizedPrimaryFreeCoefficients

/-!
# The full actual normalized primary error

Source: original lem:increments, main.tex638–661. The correction amplitude below
is the literal finite sum of actual real/imaginary corrections, with no cutoff
moved across reconstruction. The later actual-channel consumer uses canonical R
and canonical finite u, without desired-error hypotheses or alternate carriers.
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The original finite complex correction amplitude in one ambient coordinate.
Source: the P+iQ primary coefficients in original main.tex638–651. -/
def incrementsPrimaryCorrectionSum {A : Type*} [Fintype A] {n N : ℕ}
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (coord : Fin N) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ a, (incrementsFreeComplexCoordinate coord (P a x) +
    Complex.I • incrementsFreeComplexCoordinate coord (Q a x))

/-- Native finite differentiation identifies the SAME canonical correction
coefficient with its slow derivative plus its fast phase product. No averaging,
formal label equality or assumed coefficient identity is used.
Source: original main.tex645–651. -/
theorem increments_primary_correction_coefficient_eq {A : Type*} [Fintype A] {n N : ℕ}
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (hP : ∀ a, DifferentiableAt ℝ (P a) x)
    (hQ : ∀ a, DifferentiableAt ℝ (Q a) x) :
    incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q x v coord =
      fderiv ℝ (incrementsPrimaryCorrectionSum P Q coord) x v +
        Complex.I * (fderiv ℝ phi x v / tau : ℂ) * incrementsPrimaryCorrectionSum P Q coord x := by
  let C := incrementsFreeComplexCoordinate coord
  have hp (a : A) : HasFDerivAt (fun y ↦ C (P a y))
      (C.comp (fderiv ℝ (P a) x)) x := C.hasFDerivAt.comp x (hP a).hasFDerivAt
  have hq (a : A) : HasFDerivAt (fun y ↦ C (Q a y))
      (C.comp (fderiv ℝ (Q a) x)) x := C.hasFDerivAt.comp x (hQ a).hasFDerivAt
  have hd : HasFDerivAt (incrementsPrimaryCorrectionSum P Q coord)
      (∑ a, (C.comp (fderiv ℝ (P a) x) + Complex.I • C.comp (fderiv ℝ (Q a) x))) x :=
    HasFDerivAt.fun_sum fun a _ ↦ (hp a).add ((hq a).const_smul Complex.I)
  rw [hd.fderiv]
  simp only [sum_apply, add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, smul_eq_mul]
  unfold incrementsPrimaryDerivativeCoefficient incrementsPrimaryCorrectionSum
  simp only [fderiv_const_apply, zero_apply, Complex.ofReal_zero, Complex.ofReal_one,
    zero_mul, one_mul, zero_add]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  change ((fderiv ℝ (P a) x v coord : ℝ) : ℂ) +
    Complex.I * ((fderiv ℝ (Q a) x v coord : ℝ) : ℂ) +
    Complex.I * (fderiv ℝ phi x v / tau : ℂ) *
      ((P a x coord : ℂ) + Complex.I * (Q a x coord : ℂ)) = _
  rfl

/-- The entire literal normalized primary error, including BOTH free slow terms
and every real/imaginary correction derivative and fast phase term.
Source: original main.tex645–661. This is not a bound supplied as a hypothesis. -/
theorem increments_full_normalized_primary_error_eq {A : Type*} [Fintype A] {n N : ℕ}
    (tau : ℝ) (b phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (hb : DifferentiableAt ℝ b x) (hn : DifferentiableAt ℝ normal x)
    (hP : ∀ a, DifferentiableAt ℝ (P a) x)
    (hQ : ∀ a, DifferentiableAt ℝ (Q a) x) :
    incrementsPrimaryErrorCoefficient 1 tau b phi normal P Q x v coord =
      incrementsFreeComplexCoordinate coord
        (fderiv ℝ (incrementsPrimaryFreeAmplitude 1 tau b normal) x v) +
      fderiv ℝ (incrementsPrimaryCorrectionSum P Q coord) x v +
        Complex.I * (fderiv ℝ phi x v / tau : ℂ) * incrementsPrimaryCorrectionSum P Q coord x := by
  have he := increments_primary_error_free_slow_eq (A := A) tau b phi normal x v coord hb hn
  have hz : incrementsPrimaryErrorCoefficient (A := A) 1 tau b phi normal
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) x v coord =
      (Real.sqrt 2 * 1 * tau *
        (fderiv ℝ b x v * normal x coord + b x * fderiv ℝ normal x v coord) : ℝ) := by
    simp [incrementsPrimaryErrorCoefficient, incrementsPrimaryDerivativeCoefficient]
  rw [hz] at he
  rw [incrementsPrimaryErrorCoefficient, he,
    increments_primary_correction_coefficient_eq phi tau P Q x v coord hP hQ]
  exact (add_assoc _ _ _).symm

/-- The actual correction sum preserves the SAME pair of input differences.
Source: the literal P+iQ finite expression in original main.tex645–661. -/
theorem incrementsPrimaryCorrectionSum_sub {A : Type*} [Fintype A] {n N : ℕ}
    (P Q Pbar Qbar : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (coord : Fin N) :
    (fun x ↦ incrementsPrimaryCorrectionSum P Q coord x -
      incrementsPrimaryCorrectionSum Pbar Qbar coord x) =
      incrementsPrimaryCorrectionSum (fun a x ↦ P a x - Pbar a x)
        (fun a x ↦ Q a x - Qbar a x) coord := by
  funext x
  simp only [incrementsPrimaryCorrectionSum, ← Finset.sum_sub_distrib, map_sub, smul_sub]
  apply Finset.sum_congr rfl
  intro a ha
  abel

/-- Genuine local smoothness of the literal correction sum follows from the
actual correction fields, which the reconstructed-channel provider derives.
Source: finite differential construction in original main.tex638–661. -/
theorem incrementsPrimaryCorrectionSum_contDiffOn {A : Type*} [Fintype A] {n N : ℕ}
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (coord : Fin N) (O : Set (EuclideanSpace ℝ (Fin n)))
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O) :
    ContDiffOn ℝ ∞ (incrementsPrimaryCorrectionSum P Q coord) O := by
  exact ContDiffOn.sum fun a _ ↦
    ((incrementsFreeComplexCoordinate coord).contDiff.comp_contDiffOn (hP a)).add
      (((incrementsFreeComplexCoordinate coord).contDiff.comp_contDiffOn (hQ a)).const_smul
        Complex.I)

/-- Convert the actual real/imaginary reconstructed-field estimates into the
literal finite correction-amplitude estimate. These are internal producer outputs,
never new final increments hypotheses. The explicit finite-label factor is retained;
the original local-overlap uniformity caller must not identify it with a uniform bound.
Source: original main.tex645–661. -/
theorem increments_primary_correction_sum_scaled_jets {A : Type*} [Fintype A] {n N : ℕ}
    (order : ℕ) (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (coord : Fin N) (O S : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (hSO : S ⊆ O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (ell tau TP TQ : ℝ) (hell : 0 ≤ ell)
    (hPb : ∀ a, ∀ k ≤ order, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (P a) x‖ ≤ TP * tau ^ 2)
    (hQb : ∀ a, ∀ k ≤ order, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (Q a) x‖ ≤ TQ * tau ^ 2) :
    ∀ k ≤ order, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (incrementsPrimaryCorrectionSum P Q coord) x‖ ≤
        (Fintype.card A : ℝ) *
          (‖incrementsFreeComplexCoordinate coord‖ * TP +
            ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ) * tau ^ 2 := by
  let C := incrementsFreeComplexCoordinate coord
  let CI := Complex.I • C
  have hp (a : A) : ContDiffOn ℝ ∞ (fun y ↦ C (P a y)) O :=
    C.contDiff.comp_contDiffOn (hP a)
  have hq (a : A) : ContDiffOn ℝ ∞ (fun y ↦ CI (Q a y)) O :=
    CI.contDiff.comp_contDiffOn (hQ a)
  intro k hk x hx
  have hpc (a : A) : ell ^ (k + 1) *
      ‖iteratedFDeriv ℝ k (fun y ↦ C (P a y)) x‖ ≤ ‖C‖ * TP * tau ^ 2 := by
    have hh := C.norm_iteratedFDeriv_comp_left
      ((hP a).contDiffAt (hO.mem_nhds (hSO hx))) (by simp : (k : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell ^ (k + 1) * (‖C‖ * ‖iteratedFDeriv ℝ k (P a) x‖) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg hell _)
      _ = ‖C‖ * (ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (P a) x‖) := by ring
      _ ≤ ‖C‖ * (TP * tau ^ 2) :=
        mul_le_mul_of_nonneg_left (hPb a k hk x hx) (norm_nonneg C)
      _ = _ := by ring
  have hqc (a : A) : ell ^ (k + 1) *
      ‖iteratedFDeriv ℝ k (fun y ↦ CI (Q a y)) x‖ ≤ ‖CI‖ * TQ * tau ^ 2 := by
    have hh := CI.norm_iteratedFDeriv_comp_left
      ((hQ a).contDiffAt (hO.mem_nhds (hSO hx))) (by simp : (k : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell ^ (k + 1) * (‖CI‖ * ‖iteratedFDeriv ℝ k (Q a) x‖) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg hell _)
      _ = ‖CI‖ * (ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (Q a) x‖) := by ring
      _ ≤ ‖CI‖ * (TQ * tau ^ 2) :=
        mul_le_mul_of_nonneg_left (hQb a k hk x hx) (norm_nonneg CI)
      _ = _ := by ring
  have ht (a : A) : ell ^ (k + 1) *
      ‖iteratedFDeriv ℝ k (fun y ↦ C (P a y) + CI (Q a y)) x‖ ≤
        (‖C‖ * TP + ‖CI‖ * TQ) * tau ^ 2 := by
    rw [fun_iteratedFDeriv_add_apply
      (((hp a).contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))
      (((hq a).contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))]
    have hh := mul_le_mul_of_nonneg_left
      (norm_add_le (iteratedFDeriv ℝ k (fun y ↦ C (P a y)) x)
        (iteratedFDeriv ℝ k (fun y ↦ CI (Q a y)) x)) (pow_nonneg hell (k + 1))
    nlinarith [hpc a, hqc a]
  change ell ^ (k + 1) * ‖iteratedFDeriv ℝ k
    (fun y ↦ ∑ a, (C (P a y) + CI (Q a y))) x‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply (fun a _ ↦
    (((hp a).add (hq a)).contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))]
  calc
    _ ≤ ell ^ (k + 1) * ∑ a, ‖iteratedFDeriv ℝ k
        (fun y ↦ C (P a y) + CI (Q a y)) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hell _)
    _ = ∑ a, ell ^ (k + 1) * ‖iteratedFDeriv ℝ k
        (fun y ↦ C (P a y) + CI (Q a y)) x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _a : A, (‖C‖ * TP + ‖CI‖ * TQ) * tau ^ 2 :=
      Finset.sum_le_sum (fun a _ ↦ ht a)
    _ = _ := by simp; ring

/-- Actual slow and fast correction terms retain tau/ell at every observation
order. P/Q bounds here are the internal actual reconstructed-channel outputs,
which the source/geometry consumer derives; they are not final target premises.
Source: original main.tex645–661. -/
theorem increments_primary_correction_coefficient_scaled_jets
    {A : Type*} [Fintype A] {n N : ℕ} (j : ℕ)
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (O S : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (hSO : S ⊆ O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (ell tau TP TQ M : ℝ) (hell : 0 < ell) (htau : 0 < tau) (htauell : tau ≤ ell)
    (hTP : 0 ≤ TP) (hTQ : 0 ≤ TQ) (hM : 0 ≤ M)
    (hPb : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (P a) x‖ ≤ TP * tau ^ 2)
    (hQb : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (Q a) x‖ ≤ TQ * tau ^ 2)
    (hphib : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ phi y v) x‖ ≤ M) :
    let H : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight
      (Complex.I • ContinuousLinearMap.id ℝ ℂ)
    let CZ := (Fintype.card A : ℝ) *
      (‖incrementsFreeComplexCoordinate coord‖ * TP +
        ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ)
    ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q y v coord) x‖ ≤
          (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2 ^ j * ‖H‖ * M) * CZ * (tau / ell) := by
  let H : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight
    (Complex.I • ContinuousLinearMap.id ℝ ℂ)
  let Ht := (tau⁻¹ : ℝ) • H
  let CZ := (Fintype.card A : ℝ) *
    (‖incrementsFreeComplexCoordinate coord‖ * TP +
      ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ)
  let Z := incrementsPrimaryCorrectionSum P Q coord
  let g := fun y ↦ fderiv ℝ phi y v
  let Ev := ContinuousLinearMap.apply ℝ ℂ v
  have hCZ : 0 ≤ CZ := by dsimp [CZ]; positivity
  have hZ : ContDiffOn ℝ ∞ Z O := incrementsPrimaryCorrectionSum_contDiffOn P Q coord O hP hQ
  have hZb := increments_primary_correction_sum_scaled_jets (j + 1) P Q coord O S hO hSO
    hP hQ ell tau TP TQ hell.le hPb hQb
  have hg : ContDiffOn ℝ ∞ g O :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp_contDiffOn
    (hphi.fderiv_of_isOpen hO (by simp))
  have hAs : ContDiffOn ℝ ∞ (fun y ↦ Ht (g y)) O := Ht.contDiff.comp_contDiffOn hg
  have hFast : ContDiffOn ℝ ∞ (fun y ↦ Ht (g y) (Z y)) O := hAs.clm_apply hZ
  have hSlow : ContDiffOn ℝ ∞ (fun y ↦ Ev (fderiv ℝ Z y)) O :=
    Ev.contDiff.comp_contDiffOn (hZ.fderiv_of_isOpen hO (by simp))
  have hAsb : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ Ht (g y)) x‖ ≤ ‖H‖ * M / tau := by
    intro i hi x hx
    have hh := Ht.norm_iteratedFDeriv_comp_left
      (hg.contDiffAt (hO.mem_nhds (hSO hx))) (by simp : (i : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell ^ i * (‖Ht‖ * ‖iteratedFDeriv ℝ i g x‖) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ‖Ht‖ * (ell ^ i * ‖iteratedFDeriv ℝ i g x‖) := by ring
      _ ≤ ‖Ht‖ * M := mul_le_mul_of_nonneg_left (hphib i hi x hx) (norm_nonneg Ht)
      _ ≤ (tau⁻¹ * ‖H‖) * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        simpa only [Ht, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htau)] using
          ContinuousLinearMap.opNorm_smul_le (tau⁻¹ : ℝ) H
      _ = _ := by ring
  have hZb0 : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i Z x‖ ≤ CZ * tau ^ 2 / ell := by
    intro i hi x hx
    apply (le_div_iff₀ hell).2
    convert hZb i (by omega) x hx using 1; simp only [pow_succ]; ring
  have hFastb : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ Ht (g y) (Z y)) x‖ ≤
        (2 ^ j * ‖H‖ * M) * CZ * (tau / ell) := by
    intro k hk x hx
    have hh := scaled_clm_apply O hO (fun y ↦ Ht (g y)) Z hAs hZ k 0 ell
      (‖H‖ * M / tau) (CZ * tau ^ 2 / ell) hell.le
      (fun i hi ↦ hAsb i (hi.trans hk) x hx)
      (fun i hi ↦ by simpa using hZb0 i (hi.trans hk) x hx) (hSO hx)
    calc
      _ ≤ 2 ^ k * (‖H‖ * M / tau) * (CZ * tau ^ 2 / ell) := by simpa using hh
      _ = (2 ^ k * ‖H‖ * M) * CZ * (tau / ell) := by
        field_simp
      _ ≤ _ := by gcongr; norm_num
  have hSlowb : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ Ev (fderiv ℝ Z y)) x‖ ≤
        ‖Ev‖ * CZ * (tau / ell) := by
    intro k hk x hx
    have hh := Ev.norm_iteratedFDeriv_comp_left
      ((hZ.fderiv_of_isOpen hO (by simp)).contDiffAt (hO.mem_nhds (hSO hx)))
      (by simp : (k : ℕ∞ω) ≤ ∞)
    have hd : ell ^ k * ‖iteratedFDeriv ℝ k (fderiv ℝ Z) x‖ ≤ CZ * tau ^ 2 / ell ^ 2 := by
      rw [norm_iteratedFDeriv_fderiv]
      apply (le_div_iff₀ (pow_pos hell 2)).2
      convert hZb (k + 1) (by omega) x hx using 1
      simp only [pow_add]
      ring
    have hr : (tau / ell) ^ 2 ≤ tau / ell := by
      have hr0 : 0 ≤ tau / ell := by positivity
      have hr1 : tau / ell ≤ 1 := (div_le_one hell).2 htauell
      nlinarith
    calc
      _ ≤ ell ^ k * (‖Ev‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ Z) x‖) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ‖Ev‖ * (ell ^ k * ‖iteratedFDeriv ℝ k (fderiv ℝ Z) x‖) := by ring
      _ ≤ ‖Ev‖ * (CZ * tau ^ 2 / ell ^ 2) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg Ev)
      _ = (‖Ev‖ * CZ) * (tau / ell) ^ 2 := by rw [div_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (mul_nonneg (norm_nonneg Ev) hCZ)
  dsimp only
  intro k hk x hx
  have he : (fun y ↦ incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q y v coord)
      =ᶠ[𝓝 x] (fun y ↦ Ev (fderiv ℝ Z y) + Ht (g y) (Z y)) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    rw [increments_primary_correction_coefficient_eq phi tau P Q y v coord
      (fun a ↦ ((hP a).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
      (fun a ↦ ((hQ a).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))]
    congr 1
    change Complex.I * ((g y : ℂ) / (tau : ℂ)) * Z y =
      (tau⁻¹ : ℝ) • (g y • (Complex.I * Z y))
    simp only [Complex.real_smul, Complex.ofReal_inv]
    ring
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds,
    fun_iteratedFDeriv_add_apply
      ((hSlow.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))
      ((hFast.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))]
  have ht := mul_le_mul_of_nonneg_left (norm_add_le
    (iteratedFDeriv ℝ k (fun y ↦ Ev (fderiv ℝ Z y)) x)
    (iteratedFDeriv ℝ k (fun y ↦ Ht (g y) (Z y)) x)) (pow_nonneg hell.le k)
  change _ ≤ (‖Ev‖ + 2 ^ j * ‖H‖ * M) * CZ * (tau / ell)
  nlinarith [hSlowb k hk x hx, hFastb k hk x hx]

/-- SAME-input subtraction of the literal correction coefficient is justified
on the actual smooth germs, not for arbitrary totalized derivatives.
Source: original equation (6.3), main.tex654–661. -/
theorem increments_primary_correction_coefficient_sub {A : Type*} [Fintype A] {n N : ℕ}
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (tau : ℝ)
    (P Q Pbar Qbar : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (O : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hPbar : ∀ a, ContDiffOn ℝ ∞ (Pbar a) O) (hQbar : ∀ a, ContDiffOn ℝ ∞ (Qbar a) O) :
    Set.EqOn
      (fun x ↦ incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q x v coord -
        incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) Pbar Qbar x v coord)
      (fun x ↦ incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1)
        (fun a y ↦ P a y - Pbar a y) (fun a y ↦ Q a y - Qbar a y) x v coord) O := by
  intro x hx
  dsimp only
  have hp (a : A) := ((hP a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hq (a : A) := ((hQ a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hpb (a : A) := ((hPbar a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hqb (a : A) := ((hQbar a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hz := ((incrementsPrimaryCorrectionSum_contDiffOn P Q coord O hP hQ).contDiffAt
    (hO.mem_nhds hx)).differentiableAt (by simp)
  have hzb := ((incrementsPrimaryCorrectionSum_contDiffOn Pbar Qbar coord O hPbar hQbar).contDiffAt
    (hO.mem_nhds hx)).differentiableAt (by simp)
  rw [increments_primary_correction_coefficient_eq phi tau P Q x v coord hp hq,
    increments_primary_correction_coefficient_eq phi tau Pbar Qbar x v coord hpb hqb,
    increments_primary_correction_coefficient_eq phi tau
      (fun a y ↦ P a y - Pbar a y) (fun a y ↦ Q a y - Qbar a y) x v coord
      (fun a ↦ (hp a).sub (hpb a)) (fun a ↦ (hq a).sub (hqb a)),
    ← incrementsPrimaryCorrectionSum_sub P Q Pbar Qbar coord,
    fderiv_fun_sub hz hzb]
  simp only [sub_apply]
  ring

/-- The actual correction coefficient difference retains the SAME Delta and
tau/ell, with no additional input derivative order. The correction-field difference
bounds are produced from SAME actual finite sources and geometry upstream.
Source: original equation (6.3), main.tex654–661. -/
theorem increments_primary_correction_coefficient_difference_scaled_jets
    {A : Type*} [Fintype A] {n N : ℕ} (j : ℕ)
    (P Q Pbar Qbar : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (O S : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (hSO : S ⊆ O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hPbar : ∀ a, ContDiffOn ℝ ∞ (Pbar a) O) (hQbar : ∀ a, ContDiffOn ℝ ∞ (Qbar a) O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (ell tau TP TQ M Delta : ℝ) (hell : 0 < ell) (htau : 0 < tau) (htauell : tau ≤ ell)
    (hTP : 0 ≤ TP) (hTQ : 0 ≤ TQ) (hM : 0 ≤ M) (hDelta : 0 ≤ Delta)
    (hPb : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun y ↦ P a y - Pbar a y) x‖ ≤
        TP * tau ^ 2 * Delta)
    (hQb : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun y ↦ Q a y - Qbar a y) x‖ ≤
        TQ * tau ^ 2 * Delta)
    (hphib : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ phi y v) x‖ ≤ M) :
    let H : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight
      (Complex.I • ContinuousLinearMap.id ℝ ℂ)
    let CZ := (Fintype.card A : ℝ) *
      (‖incrementsFreeComplexCoordinate coord‖ * TP +
        ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ)
    ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q y v coord -
          incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) Pbar Qbar y v coord) x‖ ≤
          (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2 ^ j * ‖H‖ * M) * CZ * (tau / ell) * Delta := by
  have hh := increments_primary_correction_coefficient_scaled_jets j
    (fun a y ↦ P a y - Pbar a y) (fun a y ↦ Q a y - Qbar a y)
    phi v coord O S hO hSO (fun a ↦ (hP a).sub (hPbar a))
    (fun a ↦ (hQ a).sub (hQbar a)) hphi ell tau (TP * Delta) (TQ * Delta) M
    hell htau htauell (by positivity) (by positivity) hM
    (fun a k hk x hx ↦ by nlinarith [hPb a k hk x hx])
    (fun a k hk x hx ↦ by nlinarith [hQb a k hk x hx]) hphib
  dsimp only
  intro k hk x hx
  have he : (fun y ↦
      incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q y v coord -
        incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) Pbar Qbar y v coord)
      =ᶠ[𝓝 x] (fun y ↦ incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1)
        (fun a z ↦ P a z - Pbar a z) (fun a z ↦ Q a z - Qbar a z) y v coord) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    exact increments_primary_correction_coefficient_sub phi tau P Q Pbar Qbar v coord
      O hO hP hQ hPbar hQbar hy
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  convert hh k hk x hx using 1; ring

/-- The literal correction derivative coefficient is smooth on the SAME original
open set from actual phase/correction smoothness. Source: main.tex638–661. -/
theorem increments_primary_correction_coefficient_contDiffOn
    {A : Type*} [Fintype A] {n N : ℕ}
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (O : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hphi : ContDiffOn ℝ ∞ phi O) (tau : ℝ) :
    ContDiffOn ℝ ∞
      (fun y ↦ incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q y v coord) O := by
  let Z := incrementsPrimaryCorrectionSum P Q coord
  let H := Complex.I • Complex.ofRealCLM
  have hz : ContDiffOn ℝ ∞ Z O := incrementsPrimaryCorrectionSum_contDiffOn P Q coord O hP hQ
  have hg : ContDiffOn ℝ ∞ (fun y ↦ fderiv ℝ phi y v) O :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp_contDiffOn
      (hphi.fderiv_of_isOpen hO (by simp))
  have hs : ContDiffOn ℝ ∞ (fun y ↦ fderiv ℝ Z y v) O :=
    (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp_contDiffOn
      (hz.fderiv_of_isOpen hO (by simp))
  have ht : ContDiffOn ℝ ∞ (fun y ↦ H (fderiv ℝ phi y v / tau) * Z y) O :=
    (H.contDiff.comp_contDiffOn (hg.div_const tau)).mul hz
  apply (hs.add ht).congr
  intro x hx
  rw [increments_primary_correction_coefficient_eq phi tau P Q x v coord
    (fun a ↦ ((hP a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    (fun a ↦ ((hQ a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))]
  simp [H, Z, Complex.ofReal_div]

/-- Full canonical normalized primary error size, combining the actual free slow
derivative and every reconstructed slow/fast correction. The input amplitude and
P/Q estimates are internal outputs of the actual reserve/reconstruction providers,
not added hypotheses of the original increments target. Source: main.tex645–661. -/
theorem increments_full_normalized_primary_error_scaled_jets
    {A : Type*} [Fintype A] {n N : ℕ} (j : ℕ)
    (b phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (O S : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (hSO : S ⊆ O)
    (hb : ContDiffOn ℝ ∞ b O) (hn : ContDiffOn ℝ ∞ normal O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (ell tau Cv TP TQ M : ℝ) (hell : 0 < ell) (htau : 0 < tau) (htauell : tau ≤ ell)
    (_hCv : 0 ≤ Cv) (hTP : 0 ≤ TP) (hTQ : 0 ≤ TQ) (hM : 0 ≤ M)
    (hvb : ∀ k ≤ j + 1, ∀ x ∈ S, ell ^ k *
      ‖iteratedFDeriv ℝ k (incrementsPrimaryFreeAmplitude 1 tau b normal) x‖ ≤ Cv * tau)
    (hPb : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (P a) x‖ ≤ TP * tau ^ 2)
    (hQb : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (Q a) x‖ ≤ TQ * tau ^ 2)
    (hphib : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ phi y v) x‖ ≤ M) :
    let H : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight
      (Complex.I • ContinuousLinearMap.id ℝ ℂ)
    let CZ := (Fintype.card A : ℝ) *
      (‖incrementsFreeComplexCoordinate coord‖ * TP +
        ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ)
    let Cf := ‖(incrementsFreeComplexCoordinate coord).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) v)‖ * Cv
    ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y ↦ incrementsPrimaryErrorCoefficient 1 tau b phi normal P Q y v coord) x‖ ≤
        (Cf + (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2 ^ j * ‖H‖ * M) * CZ) * (tau / ell) := by
  let Vfree := incrementsPrimaryFreeAmplitude 1 tau b normal
  let Fv := (incrementsFreeComplexCoordinate coord).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) v)
  have hv : ContDiffOn ℝ ∞ Vfree O :=
    (hb.const_smul (Real.sqrt 2 * (1 : ℝ) * tau)).smul hn
  have hfs : ContDiffOn ℝ ∞ (fun y ↦ Fv (fderiv ℝ Vfree y)) O :=
    Fv.contDiff.comp_contDiffOn (hv.fderiv_of_isOpen hO (by simp))
  have hcs := increments_primary_correction_coefficient_contDiffOn P Q phi v coord O hO
    hP hQ hphi tau
  have hcb := increments_primary_correction_coefficient_scaled_jets j P Q phi v coord O S
    hO hSO hP hQ hphi ell tau TP TQ M hell htau htauell hTP hTQ hM hPb hQb hphib
  have hfb : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ Fv (fderiv ℝ Vfree y)) x‖ ≤
        ‖Fv‖ * Cv * (tau / ell) := by
    intro k hk x hx
    have hd : ell ^ k * ‖iteratedFDeriv ℝ k (fderiv ℝ Vfree) x‖ ≤ Cv * tau / ell := by
      rw [norm_iteratedFDeriv_fderiv]
      apply (le_div_iff₀ hell).2
      convert hvb (k + 1) (by omega) x hx using 1; simp only [pow_succ]; ring
    have hh := Fv.norm_iteratedFDeriv_comp_left
      ((hv.fderiv_of_isOpen hO (by simp)).contDiffAt (hO.mem_nhds (hSO hx)))
      (by simp : (k : ℕ∞ω) ≤ ∞)
    calc
      _ ≤ ell ^ k * (‖Fv‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ Vfree) x‖) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ‖Fv‖ * (ell ^ k * ‖iteratedFDeriv ℝ k (fderiv ℝ Vfree) x‖) := by ring
      _ ≤ ‖Fv‖ * (Cv * tau / ell) := mul_le_mul_of_nonneg_left hd (norm_nonneg Fv)
      _ = _ := by ring
  dsimp only
  intro k hk x hx
  have he : (fun y ↦ incrementsPrimaryErrorCoefficient 1 tau b phi normal P Q y v coord)
      =ᶠ[𝓝 x] (fun y ↦ Fv (fderiv ℝ Vfree y) +
        incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q y v coord) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    have hp (a : A) := ((hP a).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)
    have hq (a : A) := ((hQ a).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)
    rw [increments_full_normalized_primary_error_eq tau b phi normal P Q y v coord
      ((hb.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
      ((hn.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)) hp hq,
      increments_primary_correction_coefficient_eq phi tau P Q y v coord hp hq]
    exact add_assoc _ _ _
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds,
    fun_iteratedFDeriv_add_apply
      ((hfs.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))
      ((hcs.contDiffAt (hO.mem_nhds (hSO hx))).of_le (by simp))]
  have ht := mul_le_mul_of_nonneg_left (norm_add_le
    (iteratedFDeriv ℝ k (fun y ↦ Fv (fderiv ℝ Vfree y)) x)
    (iteratedFDeriv ℝ k (fun y ↦
      incrementsPrimaryDerivativeCoefficient phi tau (fun _ _ ↦ 1) P Q y v coord) x))
    (pow_nonneg hell.le k)
  nlinarith [hfb k hk x hx, hcb k hk x hx]

/-- The FULL normalized error subtracts on the same actual smooth germs, with
geometry and phase fixed. No totalized derivative linearity on arbitrary functions
is asserted. Source: original equation (6.3), main.tex654–661. -/
theorem increments_full_normalized_primary_error_sub
    {A : Type*} [Fintype A] {n N : ℕ}
    (b bbar phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (P Q Pbar Qbar : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (tau : ℝ) (v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (O : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O)
    (hb : ContDiffOn ℝ ∞ b O) (hbbar : ContDiffOn ℝ ∞ bbar O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hPbar : ∀ a, ContDiffOn ℝ ∞ (Pbar a) O) (hQbar : ∀ a, ContDiffOn ℝ ∞ (Qbar a) O) :
    Set.EqOn
      (fun x ↦ incrementsPrimaryErrorCoefficient 1 tau b phi normal P Q x v coord -
        incrementsPrimaryErrorCoefficient 1 tau bbar phi normal Pbar Qbar x v coord)
      (fun x ↦ incrementsPrimaryErrorCoefficient 1 tau (fun y ↦ b y - bbar y) phi normal
        (fun a y ↦ P a y - Pbar a y) (fun a y ↦ Q a y - Qbar a y) x v coord) O := by
  intro x hx
  dsimp only
  have hc := increments_primary_correction_coefficient_sub phi tau P Q Pbar Qbar v coord
    O hO hP hQ hPbar hQbar hx
  dsimp only at hc
  simp only [incrementsPrimaryErrorCoefficient]
  rw [fderiv_fun_sub ((hb.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    ((hbbar.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)), ← hc]
  simp only [sub_apply]
  push_cast
  ring

/-- FULL canonical normalized primary-error difference, with the SAME Delta and
same finite derivative loss as size. The actual reserve and reconstructed-channel
producers provide the free and P/Q differences used here, before final target
instantiation. Source: original equation (6.3), main.tex654–661. -/
theorem increments_full_normalized_primary_error_difference_scaled_jets
    {A : Type*} [Fintype A] {n N : ℕ} (j : ℕ)
    (b bbar phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (P Q Pbar Qbar : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin n)) (coord : Fin N)
    (O S : Set (EuclideanSpace ℝ (Fin n))) (hO : IsOpen O) (hSO : S ⊆ O)
    (hb : ContDiffOn ℝ ∞ b O) (hbbar : ContDiffOn ℝ ∞ bbar O)
    (hn : ContDiffOn ℝ ∞ normal O)
    (hP : ∀ a, ContDiffOn ℝ ∞ (P a) O) (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) O)
    (hPbar : ∀ a, ContDiffOn ℝ ∞ (Pbar a) O) (hQbar : ∀ a, ContDiffOn ℝ ∞ (Qbar a) O)
    (hphi : ContDiffOn ℝ ∞ phi O)
    (ell tau Cv TP TQ M Delta : ℝ) (hell : 0 < ell) (htau : 0 < tau) (htauell : tau ≤ ell)
    (hCv : 0 ≤ Cv) (hTP : 0 ≤ TP) (hTQ : 0 ≤ TQ) (hM : 0 ≤ M) (hDelta : 0 ≤ Delta)
    (hvd : ∀ k ≤ j + 1, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y ↦ incrementsPrimaryFreeAmplitude 1 tau b normal y -
        incrementsPrimaryFreeAmplitude 1 tau bbar normal y) x‖ ≤ Cv * tau * Delta)
    (hPd : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun y ↦ P a y - Pbar a y) x‖ ≤
        TP * tau ^ 2 * Delta)
    (hQd : ∀ a, ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun y ↦ Q a y - Qbar a y) x‖ ≤
        TQ * tau ^ 2 * Delta)
    (hphib : ∀ k ≤ j, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ phi y v) x‖ ≤ M) :
    let H : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight
      (Complex.I • ContinuousLinearMap.id ℝ ℂ)
    let CZ := (Fintype.card A : ℝ) *
      (‖incrementsFreeComplexCoordinate coord‖ * TP +
        ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ)
    let Cf := ‖(incrementsFreeComplexCoordinate coord).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N)) v)‖ * Cv
    ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y ↦ incrementsPrimaryErrorCoefficient 1 tau b phi normal P Q y v coord -
        incrementsPrimaryErrorCoefficient 1 tau bbar phi normal Pbar Qbar y v coord) x‖ ≤
        (Cf + (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2 ^ j * ‖H‖ * M) * CZ) *
          (tau / ell) * Delta := by
  have heV : incrementsPrimaryFreeAmplitude 1 tau (fun y ↦ b y - bbar y) normal =
      (fun y ↦ incrementsPrimaryFreeAmplitude 1 tau b normal y -
        incrementsPrimaryFreeAmplitude 1 tau bbar normal y) := by
    funext y
    simp only [incrementsPrimaryFreeAmplitude, mul_sub, sub_smul]
  have hh := increments_full_normalized_primary_error_scaled_jets j
    (fun y ↦ b y - bbar y) phi normal
    (fun a y ↦ P a y - Pbar a y) (fun a y ↦ Q a y - Qbar a y) v coord O S hO hSO
    (hb.sub hbbar) hn (fun a ↦ (hP a).sub (hPbar a))
    (fun a ↦ (hQ a).sub (hQbar a)) hphi ell tau
    (Cv * Delta) (TP * Delta) (TQ * Delta) M hell htau htauell
    (by positivity) (by positivity) (by positivity) hM
    (fun k hk x hx ↦ by rw [heV]; nlinarith [hvd k hk x hx])
    (fun a k hk x hx ↦ by nlinarith [hPd a k hk x hx])
    (fun a k hk x hx ↦ by nlinarith [hQd a k hk x hx]) hphib
  dsimp only
  intro k hk x hx
  have he : (fun y ↦ incrementsPrimaryErrorCoefficient 1 tau b phi normal P Q y v coord -
      incrementsPrimaryErrorCoefficient 1 tau bbar phi normal Pbar Qbar y v coord)
      =ᶠ[𝓝 x] (fun y ↦ incrementsPrimaryErrorCoefficient 1 tau
        (fun z ↦ b z - bbar z) phi normal
        (fun a z ↦ P a z - Pbar a z) (fun a z ↦ Q a z - Qbar a z) y v coord) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    exact increments_full_normalized_primary_error_sub b bbar phi normal P Q Pbar Qbar
      tau v coord O hO hb hbbar hP hQ hPbar hQbar hy
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  convert hh k hk x hx using 1; ring

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsPrimaryCorrectionSum
#print axioms GlobalEmbedding.Paper.incrementsPrimaryCorrectionSum_contDiffOn
#print axioms GlobalEmbedding.Paper.incrementsPrimaryCorrectionSum_sub
#print axioms GlobalEmbedding.Paper.increments_full_normalized_primary_error_eq
#print axioms GlobalEmbedding.Paper.increments_primary_correction_coefficient_eq
#print axioms GlobalEmbedding.Paper.increments_primary_correction_sum_scaled_jets

#print axioms GlobalEmbedding.Paper.increments_full_normalized_primary_error_difference_scaled_jets

#print axioms GlobalEmbedding.Paper.increments_full_normalized_primary_error_scaled_jets

#print axioms GlobalEmbedding.Paper.increments_full_normalized_primary_error_sub

#print axioms GlobalEmbedding.Paper.increments_primary_correction_coefficient_contDiffOn

#print axioms GlobalEmbedding.Paper.increments_primary_correction_coefficient_difference_scaled_jets

#print axioms GlobalEmbedding.Paper.increments_primary_correction_coefficient_scaled_jets

#print axioms GlobalEmbedding.Paper.increments_primary_correction_coefficient_sub
