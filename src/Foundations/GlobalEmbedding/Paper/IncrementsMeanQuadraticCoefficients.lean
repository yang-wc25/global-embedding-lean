import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-!
# Actual finite grouped primary quadratic coefficients

Source: `main.tex`, lem:increments645–661. Dot products are COMPLEX-BILINEAR,
not Hermitian. The same-primary opposite-sign contribution is named explicitly;
identification with the ENTIRE actual zero-frequency part still needs the original
phase-germ exclusions and support/cutoff caller, and is not defined by formal labels.
-/

noncomputable section
open scoped ComplexConjugate

namespace GlobalEmbedding.Paper

/-- The literal fast phase factor, with theta=phi/tau in the original caller. -/
def incrementsMeanPhase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- Native conjugation reverses the actual real phase. -/
theorem incrementsMeanPhase_conj (θ : ℝ) :
    conj (incrementsMeanPhase θ) = incrementsMeanPhase (-θ) := by
  unfold incrementsMeanPhase
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- Products have the literal signed SUM phase, not an abstract frequency label. -/
theorem incrementsMeanPhase_mul (θ η : ℝ) :
    incrementsMeanPhase θ * incrementsMeanPhase η = incrementsMeanPhase (θ + η) := by
  unfold incrementsMeanPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Both conjugate orderings and their exact quarter factor are retained. -/
theorem increments_mean_scalar_real_product (z w : ℂ) :
    (z.re : ℂ) * (w.re : ℂ) =
      (1 / 4 : ℂ) * (z * w + z * conj w + conj z * w + conj z * conj w) := by
  rw [Complex.re_eq_add_conj, Complex.re_eq_add_conj]
  ring

/-- Exact four actual phase functions in a scalar quadratic product. -/
theorem increments_mean_scalar_four_phases (θ η : ℝ) (a b : ℂ) :
    ((incrementsMeanPhase θ * a).re : ℂ) * ((incrementsMeanPhase η * b).re : ℂ) =
      (1 / 4 : ℂ) *
        (incrementsMeanPhase (θ + η) * (a * b) +
          incrementsMeanPhase (θ - η) * (a * conj b) +
          incrementsMeanPhase (-θ + η) * (conj a * b) +
          incrementsMeanPhase (-θ - η) * (conj a * conj b)) := by
  rw [increments_mean_scalar_real_product]
  simp only [map_mul, incrementsMeanPhase_conj]
  calc
    _ = (1 / 4 : ℂ) *
        ((incrementsMeanPhase θ * incrementsMeanPhase η) * (a * b) +
          (incrementsMeanPhase θ * incrementsMeanPhase (-η)) * (a * conj b) +
          (incrementsMeanPhase (-θ) * incrementsMeanPhase η) * (conj a * b) +
          (incrementsMeanPhase (-θ) * incrementsMeanPhase (-η)) * (conj a * conj b)) := by
      ring
    _ = _ := by simp only [incrementsMeanPhase_mul, sub_eq_add_neg]

/-- The SAME grouped real derivative vector, expressed in actual Euclidean coordinates. -/
def incrementsGroupedRealDerivative {Λ I : Type*} [Fintype Λ] {N : ℕ}
    (θ : Λ → ℝ) (D : Λ → I → Fin N → ℂ) (i : I) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun c ↦ ∑ ν, (incrementsMeanPhase (θ ν) * D ν i c).re)

/-- The real vector is literally the original half-sum of positive and conjugate modes. -/
theorem increments_grouped_real_derivative_half_sum {Λ I : Type*} [Fintype Λ] {N : ℕ}
    (θ : Λ → ℝ) (D : Λ → I → Fin N → ℂ) (i : I) (c : Fin N) :
    ((incrementsGroupedRealDerivative θ D i c : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ∑ ν, (incrementsMeanPhase (θ ν) * D ν i c +
        incrementsMeanPhase (-θ ν) * conj (D ν i c)) := by
  change ((∑ ν, (incrementsMeanPhase (θ ν) * D ν i c).re : ℝ) : ℂ) = _
  push_cast
  simp_rw [Complex.re_eq_add_conj, map_mul, incrementsMeanPhase_conj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν hν
  ring

/-- SAME-primary subordinate pieces group BEFORE coefficient extraction by actual sums. -/
theorem increments_group_subordinate_derivatives {Λ A I : Type*} [Fintype Λ] [Fintype A]
    {N : ℕ} (θ : Λ → ℝ) (D : Λ → A → I → Fin N → ℂ) (i : I) :
    WithLp.toLp 2 (fun c : Fin N ↦ ∑ ν, ∑ α,
      (incrementsMeanPhase (θ ν) * D ν α i c).re) =
      incrementsGroupedRealDerivative θ (fun ν i c ↦ ∑ α, D ν α i c) i := by
  ext c
  simp [incrementsGroupedRealDerivative, Finset.mul_sum]

/-- Exact finite expansion of the ACTUAL Euclidean quadratic derivative pairing.
Every source-slot pair, including diagonals, has the original four phases and quarter. -/
theorem increments_grouped_quadratic_four_phases {Λ I : Type*} [Fintype Λ] {N : ℕ}
    (θ : Λ → ℝ) (D : Λ → I → Fin N → ℂ) (i j : I) :
    (inner ℝ (incrementsGroupedRealDerivative θ D i)
      (incrementsGroupedRealDerivative θ D j) : ℂ) =
      ∑ ν, ∑ μ, (1 / 4 : ℂ) *
        (incrementsMeanPhase (θ ν + θ μ) * (D ν i ⬝ᵥ D μ j) +
          incrementsMeanPhase (θ ν - θ μ) * (D ν i ⬝ᵥ (fun c ↦ conj (D μ j c))) +
          incrementsMeanPhase (-θ ν + θ μ) * ((fun c ↦ conj (D ν i c)) ⬝ᵥ D μ j) +
          incrementsMeanPhase (-θ ν - θ μ) *
            ((fun c ↦ conj (D ν i c)) ⬝ᵥ (fun c ↦ conj (D μ j c)))) := by
  have hinner : (inner ℝ (incrementsGroupedRealDerivative θ D i)
      (incrementsGroupedRealDerivative θ D j) : ℂ) =
      ∑ c : Fin N, ∑ ν, ∑ μ,
        ((incrementsMeanPhase (θ ν) * D ν i c).re : ℂ) *
          ((incrementsMeanPhase (θ μ) * D μ j c).re : ℂ) := by
    simp only [incrementsGroupedRealDerivative, PiLp.inner_apply, Real.inner_apply]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    exact Finset.sum_comm
  rw [hinner, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ hμ
  simp_rw [increments_mean_scalar_four_phases]
  simp only [dotProduct, Finset.mul_sum, Finset.sum_add_distrib, mul_add]

/-- Explicit selected contribution, BEFORE any claim about actual constant phase germs.
The native dotProduct multiplies both arguments complex-linearly; conjugation is explicit. -/
def incrementsOppositePrimaryContribution {Λ I : Type*} [Fintype Λ] {N : ℕ}
    (D : Λ → I → Fin N → ℂ) (i j : I) : ℂ :=
  ∑ ν, (1 / 4 : ℂ) *
    ((D ν i ⬝ᵥ (fun c ↦ conj (D ν j c))) +
      ((fun c ↦ conj (D ν i c)) ⬝ᵥ D ν j))

/-- The selected opposite-primary terms have actual phase function ZERO, so their
phase factors disappear. This does not exclude other constant phase germs. -/
theorem increments_opposite_primary_phase_factors {Λ I : Type*} [Fintype Λ] {N : ℕ}
    (θ : Λ → ℝ) (D : Λ → I → Fin N → ℂ) (i j : I) :
    (∑ ν, (1 / 4 : ℂ) *
      (incrementsMeanPhase (θ ν - θ ν) * (D ν i ⬝ᵥ (fun c ↦ conj (D ν j c))) +
        incrementsMeanPhase (-θ ν + θ ν) * ((fun c ↦ conj (D ν i c)) ⬝ᵥ D ν j))) =
      incrementsOppositePrimaryContribution D i j := by
  simp [incrementsMeanPhase, incrementsOppositePrimaryContribution]

/-- Actual leading derivative coefficient with the ORIGINAL real normal and covector. -/
def incrementsLeadingCoefficient {I : Type*} {N : ℕ} (δ b : ℝ)
    (n : EuclideanSpace ℝ (Fin N)) (ξ : I → ℝ) (i : I) (c : Fin N) : ℂ :=
  Complex.I * (Real.sqrt 2 * δ * b * n c * ξ i : ℝ)

/-- The original unit real normal gives the exact leading opposite-pair coefficient,
including mixed source slots and diagonals. The factor1/4 and BOTH orders are essential. -/
theorem increments_leading_opposite_coefficient {I : Type*} {N : ℕ} (δ b : ℝ)
    (n : EuclideanSpace ℝ (Fin N)) (hn : ‖n‖ = 1) (ξ : I → ℝ) (i j : I) :
    (1 / 4 : ℂ) *
      ((incrementsLeadingCoefficient δ b n ξ i ⬝ᵥ
          (fun c ↦ conj (incrementsLeadingCoefficient δ b n ξ j c))) +
        ((fun c ↦ conj (incrementsLeadingCoefficient δ b n ξ i c)) ⬝ᵥ
          incrementsLeadingCoefficient δ b n ξ j)) =
      (δ ^ 2 * b ^ 2 * ξ i * ξ j : ℝ) := by
  have hs : ∑ c : Fin N, (n c) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hn]
    norm_num
  have hc : ∑ c : Fin N, ((n c : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast hs
  have hroot : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp (c : Fin N) :
      incrementsLeadingCoefficient δ b n ξ i c *
          conj (incrementsLeadingCoefficient δ b n ξ j c) +
        conj (incrementsLeadingCoefficient δ b n ξ i c) *
          incrementsLeadingCoefficient δ b n ξ j c =
      2 * (Real.sqrt 2 : ℂ) ^ 2 * δ ^ 2 * b ^ 2 * (ξ i : ℂ) * ξ j * (n c : ℂ) ^ 2 := by
    simp [incrementsLeadingCoefficient, map_mul]
    ring_nf
    simp
  rw [dotProduct, dotProduct, ← Finset.sum_add_distrib]
  simp_rw [hp]
  rw [← Finset.mul_sum, hc, hroot]
  push_cast
  ring

/-- Summing the ORIGINAL prescribed tensor decomposition gives delta squared A,
without taking the desired zero coefficient or a mean bound as an input. -/
theorem increments_leading_opposite_decomposition {Λ I : Type*} [Fintype Λ] {N : ℕ}
    (δ : ℝ) (b : Λ → ℝ) (n : Λ → EuclideanSpace ℝ (Fin N))
    (hn : ∀ ν, ‖n ν‖ = 1) (ξ : Λ → I → ℝ) (A : I → I → ℝ)
    (hA : ∀ i j, ∑ ν, (b ν) ^ 2 * ξ ν i * ξ ν j = A i j) (i j : I) :
    incrementsOppositePrimaryContribution
      (fun ν ↦ incrementsLeadingCoefficient δ (b ν) (n ν) (ξ ν)) i j =
        (δ ^ 2 * A i j : ℝ) := by
  unfold incrementsOppositePrimaryContribution
  simp_rw [increments_leading_opposite_coefficient δ _ _ (hn _) _ i j]
  rw [← Complex.ofReal_sum]
  apply congrArg (fun x : ℝ ↦ (x : ℂ))
  calc
    _ = δ ^ 2 * ∑ ν, (b ν) ^ 2 * ξ ν i * ξ ν j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      ring
    _ = _ := by rw [hA]

end GlobalEmbedding.Paper
