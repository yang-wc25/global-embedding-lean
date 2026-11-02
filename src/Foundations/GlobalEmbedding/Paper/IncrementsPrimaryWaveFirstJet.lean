import GlobalEmbedding.Paper.IncrementsOscillatoryFirstJet
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring

/-!
# The literal finite primary-wave first jet

Source: `main.tex`, lem:increments617–650. Differentiate the actual finite real-wave sum,
including ordinary subordinate cutoffs. The accepted single-mode first jet supplies the
phase differentiation. No zero-phase extraction or quantitative error estimate is asserted.
-/

noncomputable section
open Filter
open scoped Topology

namespace GlobalEmbedding.Paper

/-- The original primary scalar amplitude is cutoff*sqrt(positive coefficient).
Its actual product/chain derivative retains cutoff variation even where cutoff=0;
positivity is required only of the square-root argument, as in the paper. -/
theorem increments_primary_cutoff_sqrt_first_jet {n : ℕ}
    (cutoff a : EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n))
    (hcutoff : DifferentiableAt ℝ cutoff x) (ha : DifferentiableAt ℝ a x)
    (hpos : 0 < a x) :
    DifferentiableAt ℝ (fun y ↦ cutoff y * Real.sqrt (a y)) x ∧
      fderiv ℝ (fun y ↦ cutoff y * Real.sqrt (a y)) x v =
        fderiv ℝ cutoff x v * Real.sqrt (a x) +
          cutoff x * (fderiv ℝ a x v / (2 * Real.sqrt (a x))) := by
  have hd := hcutoff.hasFDerivAt.mul (ha.hasFDerivAt.sqrt hpos.ne')
  change HasFDerivAt (fun y ↦ cutoff y * Real.sqrt (a y)) _ x at hd
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The literal original primary sum, with subordinate pieces sharing the SAME phase.
P and Q are the actual real and imaginary amplitude fields, before taking real parts. -/
def incrementsPrimaryWave {Λ A : Type*} [Fintype Λ] [Fintype A] {n N : ℕ}
    (φ : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (χ : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin N) :=
  ∑ ν, ∑ α, χ ν α y • WithLp.toLp 2 (fun c : Fin N ↦
    (Complex.exp (((φ ν y / τ : ℝ) : ℂ) * Complex.I) *
      ((P ν α y c : ℂ) + Complex.I * (Q ν α y c : ℂ))).re)

/-- The already used pointwise real-mode formula, exposed for ordinary reuse.
This is the existing literal exponential-to-cosine/sine identity; no smoothness
or nonzero scale is required. Source: original primary waves, main.tex646–650. -/
theorem increments_primary_real_mode_eq {n N : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)) :
    (fun y ↦ WithLp.toLp 2 (fun c : Fin N ↦
      (Complex.exp (((φ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y c : ℂ) + Complex.I * (Q y c : ℂ))).re)) =
      fun y ↦ Real.cos (φ y / τ) • P y - Real.sin (φ y / τ) • Q y := by
  funext y
  ext c
  change (Complex.exp (((φ y / τ : ℝ) : ℂ) * Complex.I) *
    ((P y c : ℂ) + Complex.I * (Q y c : ℂ))).re = _
  rw [Complex.exp_ofReal_mul_I (φ y / τ)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

private theorem primary_real_mode_differentiableAt {n N : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin n)) (hφ : DifferentiableAt ℝ φ x)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x) :
    DifferentiableAt ℝ (fun y ↦ WithLp.toLp 2 (fun c : Fin N ↦
      (Complex.exp (((φ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y c : ℂ) + Complex.I * (Q y c : ℂ))).re)) x := by
  have heq := increments_primary_real_mode_eq φ τ P Q
  rw [heq]
  have ht : DifferentiableAt ℝ (fun y ↦ φ y / τ) x := by
    have hh := hφ.const_smul τ⁻¹
    change DifferentiableAt ℝ (fun y ↦ τ⁻¹ * φ y) x at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hc : DifferentiableAt ℝ (fun y ↦ Real.cos (φ y / τ)) x := ht.cos
  have hs : DifferentiableAt ℝ (fun y ↦ Real.sin (φ y / τ)) x := ht.sin
  exact (hc.smul hP).sub (hs.smul hQ)

/-- Actual finite primary differentiation, retaining every cutoff product term.
No partition or derivative identity is assumed. Phase derivatives are reused from
`increments_scaled_oscillatory_first_jet`, not recomputed. -/
theorem increments_primary_wave_first_jet {Λ A : Type*} [Fintype Λ] [Fintype A]
    {n N : ℕ} (φ : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (χ : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ ν : Λ, DifferentiableAt ℝ (φ ν) x)
    (hχ : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (χ ν α) x)
    (hP : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (P ν α) x)
    (hQ : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (Q ν α) x) :
    fderiv ℝ (incrementsPrimaryWave φ τ χ P Q) x v =
      Finset.univ.sum (fun ν : Λ ↦ Finset.univ.sum (fun α : A ↦
        (fderiv ℝ (χ ν α) x v) • WithLp.toLp 2 (fun c : Fin N ↦
          (Complex.exp (((φ ν x / τ : ℝ) : ℂ) * Complex.I) *
            ((P ν α x c : ℂ) + Complex.I * (Q ν α x c : ℂ))).re) +
        χ ν α x • (Real.cos (φ ν x / τ) • (fderiv ℝ (P ν α) x v) -
          Real.sin (φ ν x / τ) • (fderiv ℝ (Q ν α) x v) -
          (fderiv ℝ (φ ν) x v / τ) •
            (Real.sin (φ ν x / τ) • (P ν α x) +
              Real.cos (φ ν x / τ) • (Q ν α x))))) := by
  classical
  let W := fun (ν : Λ) (α : A) (y : EuclideanSpace ℝ (Fin n)) ↦
    WithLp.toLp 2 (fun c : Fin N ↦
    (Complex.exp (((φ ν y / τ : ℝ) : ℂ) * Complex.I) *
      ((P ν α y c : ℂ) + Complex.I * (Q ν α y c : ℂ))).re)
  have hW (ν : Λ) (α : A) : DifferentiableAt ℝ (W ν α) x :=
    primary_real_mode_differentiableAt _ _ _ _ x (hφ ν) (hP ν α) (hQ ν α)
  have hd (ν : Λ) (α : A) := ((hχ ν α).hasFDerivAt.smul (hW ν α).hasFDerivAt)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun ν _ ↦
    HasFDerivAt.fun_sum (u := Finset.univ) fun α _ ↦ hd ν α
  change HasFDerivAt (incrementsPrimaryWave φ τ χ P Q) _ x at hs
  rw [hs.fderiv]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro ν hν
  apply Finset.sum_congr rfl
  intro α hα
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  rw [show fderiv ℝ (W ν α) x v = _ from
    increments_scaled_oscillatory_first_jet (φ ν) τ (P ν α) (Q ν α) x v
      (hφ ν) (hP ν α) (hQ ν α)]
  exact add_comm _ _

/-- An ordinary partition on a neighborhood gives BOTH its value and its derivative
sum. The derivative identity is derived from the actual equal germ, not assumed. -/
theorem increments_partition_first_jet {A : Type*} [Fintype A] {n : ℕ}
    (χ : A → EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n))
    (hχ : ∀ α, DifferentiableAt ℝ (χ α) x)
    (hpartition : ∀ᶠ y in 𝓝 x, ∑ α, χ α y = 1) :
    (∑ α, χ α x) = 1 ∧ (∑ α, fderiv ℝ (χ α) x v) = 0 := by
  classical
  refine ⟨hpartition.self_of_nhds, ?_⟩
  have he : (fun y ↦ ∑ α, χ α y) =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := hpartition
  have heq := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_sum (fun α _ ↦ hχ α), fderiv_fun_const] at heq
  have hv := congrArg (fun L ↦ L v) heq
  simpa only [sum_apply, Pi.zero_apply, zero_apply] using hv

/-- The ORIGINAL real free amplitude, with its external delta*tau factor intact. -/
def incrementsPrimaryFreeAmplitude {n N : ℕ} (δ τ : ℝ)
    (b : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin N) :=
  (Real.sqrt 2 * δ * τ * b y) • normal y

/-- Differentiate the actual amplitude: both the scalar amplitude and normal field
vary. No unit-normal, phase or geometric cancellation is needed for this identity. -/
theorem increments_primary_free_amplitude_first_jet {n N : ℕ} (δ τ : ℝ)
    (b : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (hb : DifferentiableAt ℝ b x)
    (hnormal : DifferentiableAt ℝ normal x) :
    fderiv ℝ (incrementsPrimaryFreeAmplitude δ τ b normal) x v =
      (Real.sqrt 2 * δ * τ * fderiv ℝ b x v) • normal x +
      (Real.sqrt 2 * δ * τ * b x) • fderiv ℝ normal x v := by
  have ha := hb.hasFDerivAt.const_smul (Real.sqrt 2 * δ * τ)
  have hd := (ha.smul hnormal.hasFDerivAt).fderiv
  change fderiv ℝ (incrementsPrimaryFreeAmplitude δ τ b normal) x = _ at hd
  rw [hd]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  exact add_comm _ _

/-- The actual derivative coefficient, grouped by original primary phase AFTER
differentiation. Both cutoff derivatives and both complex amplitude components occur. -/
def incrementsPrimaryDerivativeCoefficient {A : Type*} [Fintype A] {n N : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (χ : A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (c : Fin N) : ℂ :=
  Finset.univ.sum (fun α : A ↦
    (fderiv ℝ (χ α) x v : ℂ) * ((P α x c : ℂ) + Complex.I * (Q α x c : ℂ)) +
    (χ α x : ℂ) * (((fderiv ℝ (P α) x v c : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ (Q α) x v c : ℝ) : ℂ) +
      Complex.I * (fderiv ℝ φ x v / τ : ℂ) *
        ((P α x c : ℂ) + Complex.I * (Q α x c : ℂ))))

private theorem primary_real_coefficient_identity (θ w χ dχ p q dp dq : ℝ) :
    dχ * (Complex.exp ((θ : ℂ) * Complex.I) * ((p : ℂ) + Complex.I * (q : ℂ))).re +
      χ * (Real.cos θ * dp - Real.sin θ * dq - w * (Real.sin θ * p + Real.cos θ * q)) =
    (Complex.exp ((θ : ℂ) * Complex.I) *
      ((dχ : ℂ) * ((p : ℂ) + Complex.I * (q : ℂ)) +
        (χ : ℂ) * ((dp : ℂ) + Complex.I * (dq : ℂ) +
          Complex.I * (w : ℂ) * ((p : ℂ) + Complex.I * (q : ℂ))))).re := by
  rw [Complex.exp_ofReal_mul_I θ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The derivative of the LITERAL real-wave sum equals its actual complex coefficient
sum. This supplies the original grouped-derivative caller without assuming that identity. -/
theorem increments_primary_wave_grouped_derivative {Λ A : Type*} [Fintype Λ] [Fintype A]
    {n N : ℕ} (φ : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (χ : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ ν : Λ, DifferentiableAt ℝ (φ ν) x)
    (hχ : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (χ ν α) x)
    (hP : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (P ν α) x)
    (hQ : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (Q ν α) x) :
    fderiv ℝ (incrementsPrimaryWave φ τ χ P Q) x v =
      WithLp.toLp 2 (fun c : Fin N ↦ ∑ ν,
        (Complex.exp (((φ ν x / τ : ℝ) : ℂ) * Complex.I) *
          incrementsPrimaryDerivativeCoefficient (φ ν) τ (χ ν) (P ν) (Q ν) x v c).re) := by
  classical
  rw [increments_primary_wave_first_jet φ τ χ P Q x v hφ hχ hP hQ]
  ext c
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
    WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, incrementsPrimaryDerivativeCoefficient, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ν hν
  apply Finset.sum_congr rfl
  intro α hα
  simpa only [Complex.ofReal_div] using primary_real_coefficient_identity
    (φ ν x / τ) (fderiv ℝ (φ ν) x v / τ) (χ ν α x) (fderiv ℝ (χ ν α) x v)
    (P ν α x c) (Q ν α x c) (fderiv ℝ (P ν α) x v c) (fderiv ℝ (Q ν α) x v c)

/-- Ordinary subordinate partitioning recovers the SAME uncut free field in the
actual derivative coefficient. Both the partition value and derivative cancellation
come from its original neighborhood identity. -/
theorem increments_primary_coefficient_add_free {A : Type*} [Fintype A] {n N : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (χ : A → EuclideanSpace ℝ (Fin n) → ℝ)
    (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (c : Fin N)
    (hχ : ∀ α, DifferentiableAt ℝ (χ α) x) (hV : DifferentiableAt ℝ V x)
    (hP : ∀ α, DifferentiableAt ℝ (P α) x)
    (hpartition : ∀ᶠ y in 𝓝 x, ∑ α, χ α y = 1) :
    incrementsPrimaryDerivativeCoefficient φ τ (fun _ _ ↦ 1)
        (fun α y ↦ χ α y • V y + P α y) Q x v c =
      (fderiv ℝ V x v c : ℂ) + Complex.I * (fderiv ℝ φ x v / τ : ℂ) * (V x c : ℂ) +
        incrementsPrimaryDerivativeCoefficient φ τ (fun _ _ ↦ 1) P Q x v c := by
  classical
  have hp := increments_partition_first_jet χ x v hχ hpartition
  have hχ0 : ∑ α, (fderiv ℝ (χ α) x v : ℂ) = 0 := by exact_mod_cast hp.2
  have hχ1 : ∑ α, (χ α x : ℂ) = 1 := by exact_mod_cast hp.1
  have hfd (α : A) : fderiv ℝ (fun y ↦ χ α y • V y + P α y) x v c =
      fderiv ℝ (χ α) x v * V x c + χ α x * fderiv ℝ V x v c +
        fderiv ℝ (P α) x v c := by
    have hd := ((hχ α).hasFDerivAt.smul hV.hasFDerivAt).add (hP α).hasFDerivAt
    change HasFDerivAt (fun y ↦ χ α y • V y + P α y) _ x at hd
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ)) x v = 0 := by
    rw [fderiv_fun_const]
    rfl
  unfold incrementsPrimaryDerivativeCoefficient
  simp only [hfd, hzero, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_zero,
    Complex.ofReal_one, zero_mul, one_mul, zero_add]
  have hterm (α : A) :
      (fderiv ℝ (χ α) x v : ℂ) * (V x c : ℂ) +
        (χ α x : ℂ) * (fderiv ℝ V x v c : ℂ) + (fderiv ℝ (P α) x v c : ℂ) +
        Complex.I * (fderiv ℝ (Q α) x v c : ℂ) +
        Complex.I * (fderiv ℝ φ x v / τ : ℂ) *
          ((χ α x : ℂ) * (V x c : ℂ) + (P α x c : ℂ) +
            Complex.I * (Q α x c : ℂ)) =
      (fderiv ℝ (χ α) x v : ℂ) * (V x c : ℂ) +
        (χ α x : ℂ) * ((fderiv ℝ V x v c : ℂ) +
          Complex.I * (fderiv ℝ φ x v / τ : ℂ) * (V x c : ℂ)) +
        ((fderiv ℝ (P α) x v c : ℂ) + Complex.I * (fderiv ℝ (Q α) x v c : ℂ) +
          Complex.I * (fderiv ℝ φ x v / τ : ℂ) *
            ((P α x c : ℂ) + Complex.I * (Q α x c : ℂ))) := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, hχ0, hχ1]
  ring

/-- The literal remaining primary derivative terms: slow amplitude/normal derivatives
and all subordinate reconstruction/cutoff derivatives. No size estimate is built in. -/
def incrementsPrimaryErrorCoefficient {A : Type*} [Fintype A] {n N : ℕ} (δ τ : ℝ)
    (b φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (c : Fin N) : ℂ :=
  (Real.sqrt 2 * δ * τ *
    (fderiv ℝ b x v * normal x c + b x * fderiv ℝ normal x v c) : ℝ) +
      incrementsPrimaryDerivativeCoefficient φ τ (fun _ _ ↦ 1) P Q x v c

/-- The actual free amplitude recovers precisely i*sqrt2*delta*b*n*dphi.
The displayed error retains every slow and reconstruction derivative. The only
division cancellation uses the original tau!=0, never an assumed leading identity. -/
theorem increments_primary_coefficient_leading {A : Type*} [Fintype A] {n N : ℕ}
    (δ τ : ℝ) (hτ : τ ≠ 0) (b φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (χ : A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (c : Fin N)
    (hb : DifferentiableAt ℝ b x) (hnormal : DifferentiableAt ℝ normal x)
    (hχ : ∀ α, DifferentiableAt ℝ (χ α) x)
    (hP : ∀ α, DifferentiableAt ℝ (P α) x)
    (hpartition : ∀ᶠ y in 𝓝 x, ∑ α, χ α y = 1) :
    incrementsPrimaryDerivativeCoefficient φ τ (fun _ _ ↦ 1)
        (fun α y ↦ χ α y • incrementsPrimaryFreeAmplitude δ τ b normal y + P α y)
        Q x v c =
      Complex.I * (Real.sqrt 2 * δ * b x * normal x c * fderiv ℝ φ x v : ℝ) +
        incrementsPrimaryErrorCoefficient δ τ b φ normal P Q x v c := by
  have hV : DifferentiableAt ℝ (incrementsPrimaryFreeAmplitude δ τ b normal) x := by
    exact (hb.const_smul (Real.sqrt 2 * δ * τ)).smul hnormal
  rw [increments_primary_coefficient_add_free φ τ χ _ P Q x v c hχ hV hP hpartition]
  have hc : (fderiv ℝ φ x v / τ) *
      incrementsPrimaryFreeAmplitude δ τ b normal x c =
      Real.sqrt 2 * δ * b x * normal x c * fderiv ℝ φ x v := by
    change (fderiv ℝ φ x v / τ) * ((Real.sqrt 2 * δ * τ * b x) * normal x c) = _
    field_simp
  have hfast : Complex.I * (fderiv ℝ φ x v / τ : ℂ) *
      (incrementsPrimaryFreeAmplitude δ τ b normal x c : ℂ) =
      Complex.I * (Real.sqrt 2 * δ * b x * normal x c * fderiv ℝ φ x v : ℝ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, mul_assoc] using
      congrArg (fun r : ℝ ↦ Complex.I * (r : ℂ)) hc
  rw [hfast, increments_primary_free_amplitude_first_jet δ τ b normal x v hb hnormal]
  simp only [incrementsPrimaryErrorCoefficient, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The literal constructed PRIMARY U1 derivative, with the original leading coefficient
and every amplitude/cutoff/normal/phase/reconstruction term. This is an identity of the
actual finite real sum; no desired derivative, zero-phase or metric estimate is assumed. -/
theorem increments_primary_homogeneous_wave_first_jet {Λ A : Type*}
    [Fintype Λ] [Fintype A] {n N : ℕ} (δ τ : ℝ) (hτ : τ ≠ 0)
    (b φ : Λ → EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : Λ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (χ : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n))
    (hb : ∀ ν : Λ, DifferentiableAt ℝ (b ν) x)
    (hφ : ∀ ν : Λ, DifferentiableAt ℝ (φ ν) x)
    (hnormal : ∀ ν : Λ, DifferentiableAt ℝ (normal ν) x)
    (hχ : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (χ ν α) x)
    (hP : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (P ν α) x)
    (hQ : ∀ (ν : Λ) (α : A), DifferentiableAt ℝ (Q ν α) x)
    (hpartition : ∀ ν : Λ, ∀ᶠ y in 𝓝 x, ∑ α, χ ν α y = 1) :
    fderiv ℝ (incrementsPrimaryWave φ τ (fun _ _ _ ↦ 1)
      (fun ν α y ↦ χ ν α y • incrementsPrimaryFreeAmplitude δ τ (b ν) (normal ν) y +
        P ν α y) Q)
        x v = WithLp.toLp 2 (fun c : Fin N ↦ ∑ ν,
          (Complex.exp (((φ ν x / τ : ℝ) : ℂ) * Complex.I) *
            (Complex.I * (Real.sqrt 2 * δ * b ν x * normal ν x c *
              fderiv ℝ (φ ν) x v : ℝ) +
              incrementsPrimaryErrorCoefficient δ τ (b ν) (φ ν) (normal ν)
                (P ν) (Q ν) x v c)).re) := by
  have hV (ν : Λ) : DifferentiableAt ℝ
      (incrementsPrimaryFreeAmplitude δ τ (b ν) (normal ν)) x := by
    exact ((hb ν).const_smul (Real.sqrt 2 * δ * τ)).smul (hnormal ν)
  rw [increments_primary_wave_grouped_derivative φ τ (fun _ _ _ ↦ 1)
    (fun ν α y ↦ χ ν α y • incrementsPrimaryFreeAmplitude δ τ (b ν) (normal ν) y +
      P ν α y)
    Q x v hφ (fun _ _ ↦ differentiableAt_const 1)
    (fun ν α ↦ ((hχ ν α).smul (hV ν)).add (hP ν α)) hQ]
  simp_rw [increments_primary_coefficient_leading δ τ hτ _ _ _ _ _ _ x v _
    (hb _) (hnormal _) (hχ _) (hP _) (hpartition _)]

end GlobalEmbedding.Paper
