import GlobalEmbedding.Paper.IncrementsMeanQuadraticCoefficients
import GlobalEmbedding.Paper.IncrementsPrimaryWaveFirstJet

/-!
# Actual phase germs in the finite primary quadratic expansion

Source: `main.tex`, lem:increments599,645–655. Noncriticality excludes equality on a
neighborhood to ANY constant. All selections below concern actual real phase germs,
with original primary labels and original amplitude supports, not formal frequencies.
-/

noncomputable section
open Filter
open scoped Topology ComplexConjugate

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero actual differential excludes every constant germ, including nonzero
constants. Native derivative locality and the derivative of a constant suffice. -/
theorem increments_noncritical_not_constant_germ (ψ : E → ℝ) (x : E)
    (hψ : fderiv ℝ ψ x ≠ 0) (c : ℝ) :
    ¬ (ψ =ᶠ[𝓝 x] fun _ ↦ c) := by
  intro h
  apply hψ
  simpa only [fderiv_fun_const, Pi.zero_apply] using h.fderiv_eq (𝕜 := ℝ)

omit [NormedSpace ℝ E] in
/-- Actual negation preserves equality of a phase germ to ZERO. -/
theorem increments_neg_zero_germ_iff (ψ : E → ℝ) (x : E) :
    ((fun y ↦ -ψ y) =ᶠ[𝓝 x] fun _ ↦ 0) ↔ (ψ =ᶠ[𝓝 x] fun _ ↦ 0) := by
  constructor
  · intro h
    filter_upwards [h] with y hy
    exact neg_eq_zero.mp hy
  · intro h
    filter_upwards [h] with y hy
    simp only [hy, neg_zero]

omit [NormedSpace ℝ E] in
/-- The original nonzero frequency scale preserves actual ZERO phase germs. -/
theorem increments_div_zero_germ_iff (ψ : E → ℝ) (τ : ℝ) (hτ : τ ≠ 0) (x : E) :
    ((fun y ↦ ψ y / τ) =ᶠ[𝓝 x] fun _ ↦ 0) ↔ (ψ =ᶠ[𝓝 x] fun _ ↦ 0) := by
  constructor
  · intro h
    filter_upwards [h] with y hy
    exact (div_eq_zero_iff.mp hy).resolve_right hτ
  · intro h
    filter_upwards [h] with y hy
    simp only [hy, zero_div]

/-- The actual fast phase also has no constant germ whenever the original phase is
noncritical and tau!=0. In particular nonzero constant phases cannot be overlooked. -/
theorem increments_noncritical_not_div_constant_germ (ψ : E → ℝ) (τ : ℝ)
    (hτ : τ ≠ 0) (x : E) (hψ : fderiv ℝ ψ x ≠ 0) (c : ℝ) :
    ¬ ((fun y ↦ ψ y / τ) =ᶠ[𝓝 x] fun _ ↦ c) := by
  intro h
  apply increments_noncritical_not_constant_germ ψ x hψ (c * τ)
  filter_upwards [h] with y hy
  exact (div_eq_iff hτ).mp hy

/-- The SAME actual differentiated complex wave coefficient is supported in the
original amplitude's topological support. Native derivative support is used directly;
no smoothness, phase separation or desired support identity is assumed. Directions
may vary with x, so this applies to actual source coordinate vector fields as well. -/
theorem increments_wave_coefficient_tsupport {N : ℕ} (Z : E → Fin N → ℂ)
    (ψ : E → ℝ) (τ : ℝ) (v : E → E) :
    tsupport (fun x ↦ fun c : Fin N ↦ fderiv ℝ Z x (v x) c +
      Complex.I * (fderiv ℝ ψ x (v x) / τ : ℂ) * Z x c) ⊆ tsupport Z := by
  apply closure_minimal _ (isClosed_tsupport Z)
  intro x hx
  by_contra hz
  have hZ := image_eq_zero_of_notMem_tsupport hz
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hz
  apply hx
  funext c
  simp only [hZ, hd, zero_apply, Pi.zero_apply, mul_zero, add_zero]

/-- Select the actual ZERO-germ terms in ONE pair of the already-proved four-phase
expansion. Tests concern actual phase functions on a neighborhood of x; both original
conjugate orderings and their quarter are retained. This is coefficient extraction,
not averaging, and does not define ZERO phase by equality of primary labels. -/
def incrementsFourPhaseZeroGermPair {Λ I : Type*} {N : ℕ}
    (φ : Λ → E → ℝ) (D : Λ → I → Fin N → ℂ) (x : E) (ν μ : Λ) (i j : I) : ℂ := by
  classical
  exact (1 / 4 : ℂ) *
    ((if (fun y ↦ φ ν y + φ μ y) =ᶠ[𝓝 x] (fun _ ↦ 0) then D ν i ⬝ᵥ D μ j else 0) +
      (if (fun y ↦ φ ν y - φ μ y) =ᶠ[𝓝 x] (fun _ ↦ 0) then
        D ν i ⬝ᵥ (fun c ↦ conj (D μ j c)) else 0) +
      (if (fun y ↦ -φ ν y + φ μ y) =ᶠ[𝓝 x] (fun _ ↦ 0) then
        (fun c ↦ conj (D ν i c)) ⬝ᵥ D μ j else 0) +
      (if (fun y ↦ -φ ν y - φ μ y) =ᶠ[𝓝 x] (fun _ ↦ 0) then
        (fun c ↦ conj (D ν i c)) ⬝ᵥ (fun c ↦ conj (D μ j c)) else 0))

omit [NormedSpace ℝ E] in
/-- The selector for the actual FAST phases phi/tau is exactly the selector for
the original slow phases. Nonzero tau is the original frequency assumption. -/
theorem increments_four_phase_zero_germ_pair_div {Λ I : Type*} {N : ℕ}
    (φ : Λ → E → ℝ) (τ : ℝ) (hτ : τ ≠ 0) (D : Λ → I → Fin N → ℂ)
    (x : E) (ν μ : Λ) (i j : I) :
    incrementsFourPhaseZeroGermPair (fun ν y ↦ φ ν y / τ) D x ν μ i j =
      incrementsFourPhaseZeroGermPair φ D x ν μ i j := by
  have hg (ψ : E → ℝ) := increments_div_zero_germ_iff ψ τ hτ x
  have hpp : (fun y ↦ φ ν y / τ + φ μ y / τ) = fun y ↦ (φ ν y + φ μ y) / τ := by
    funext y
    simp only [add_div]
  have hpm : (fun y ↦ φ ν y / τ - φ μ y / τ) = fun y ↦ (φ ν y - φ μ y) / τ := by
    funext y
    simp only [sub_div]
  have hmp : (fun y ↦ -(φ ν y / τ) + φ μ y / τ) = fun y ↦ (-φ ν y + φ μ y) / τ := by
    funext y
    simp only [add_div, neg_div]
  have hmm : (fun y ↦ -(φ ν y / τ) - φ μ y / τ) = fun y ↦ (-φ ν y - φ μ y) / τ := by
    funext y
    simp only [sub_div, neg_div]
  unfold incrementsFourPhaseZeroGermPair
  rw [hpp, hpm, hmp, hmm, hg, hg, hg, hg]

/-- Actual original overlap/noncritical data suffice for the finite ZERO-germ
extraction. The coefficient support input is an internal caller obligation; the actual
wave adapter below derives it from the SAME amplitude supports. No nonresonance beyond
the original doubled and interacting sum/difference hypotheses is introduced. -/
theorem increments_four_phase_zero_germ_eq_opposite {Λ I : Type*} [Fintype Λ] {N : ℕ}
    (φ : Λ → E → ℝ) (D : Λ → I → Fin N → ℂ) (S : Λ → Set E) (x : E)
    (hsupport : ∀ ν, x ∉ S ν → ∀ i, D ν i = 0)
    (hdouble : ∀ ν, x ∈ S ν → fderiv ℝ (fun y ↦ φ ν y + φ ν y) x ≠ 0)
    (hinteraction : ∀ ν μ, ν ≠ μ → x ∈ S ν → x ∈ S μ →
      fderiv ℝ (fun y ↦ φ ν y + φ μ y) x ≠ 0 ∧
        fderiv ℝ (fun y ↦ φ ν y - φ μ y) x ≠ 0) (i j : I) :
    (∑ ν, ∑ μ, incrementsFourPhaseZeroGermPair φ D x ν μ i j) =
      incrementsOppositePrimaryContribution D i j := by
  classical
  have hnegative (ν μ : Λ) :
      (fun y ↦ -φ ν y - φ μ y) = fun y ↦ -(φ ν y + φ μ y) := by
    funext y
    ring
  have hreverse (ν μ : Λ) :
      (fun y ↦ -φ ν y + φ μ y) = fun y ↦ -(φ ν y - φ μ y) := by
    funext y
    ring
  have hpair (ν μ : Λ) : incrementsFourPhaseZeroGermPair φ D x ν μ i j =
      if ν = μ then (1 / 4 : ℂ) *
        ((D ν i ⬝ᵥ (fun c ↦ conj (D ν j c))) +
          ((fun c ↦ conj (D ν i c)) ⬝ᵥ D ν j)) else 0 := by
    by_cases hxν : x ∈ S ν
    · by_cases hxμ : x ∈ S μ
      · by_cases hνμ : ν = μ
        · subst μ
          have hplus := increments_noncritical_not_constant_germ _ x (hdouble ν hxν) 0
          have hminus : ¬ ((fun y ↦ -φ ν y - φ ν y) =ᶠ[𝓝 x] fun _ ↦ 0) := by
            rw [hnegative, increments_neg_zero_germ_iff]
            exact hplus
          simp [incrementsFourPhaseZeroGermPair, hplus, hminus]
        · have hn := hinteraction ν μ hνμ hxν hxμ
          have hplus := increments_noncritical_not_constant_germ _ x hn.1 0
          have hdiff := increments_noncritical_not_constant_germ _ x hn.2 0
          have hminus : ¬ ((fun y ↦ -φ ν y - φ μ y) =ᶠ[𝓝 x] fun _ ↦ 0) := by
            rw [hnegative, increments_neg_zero_germ_iff]
            exact hplus
          have hrev : ¬ ((fun y ↦ -φ ν y + φ μ y) =ᶠ[𝓝 x] fun _ ↦ 0) := by
            rw [hreverse, increments_neg_zero_germ_iff]
            exact hdiff
          simp [incrementsFourPhaseZeroGermPair, hplus, hdiff, hrev, hminus, hνμ]
      · have hzero := hsupport μ hxμ j
        have hνμ : ν ≠ μ := by intro h; exact hxμ (h ▸ hxν)
        simp [incrementsFourPhaseZeroGermPair, hzero, hνμ, dotProduct]
    · have hzero := hsupport ν hxν i
      simp [incrementsFourPhaseZeroGermPair, hzero, dotProduct]
  simp_rw [hpair]
  simp [incrementsOppositePrimaryContribution]

/-- Actual localization of the FREE input preserves the original cutoff/correction
supports. The correction is NOT assumed divisible by the cutoff. Only native support
of addition and scalar multiplication is used. -/
theorem increments_localized_primary_amplitude_tsupport {n N : ℕ} (δ τ : ℝ)
    (b χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)) :
    tsupport (fun y ↦ χ y • incrementsPrimaryFreeAmplitude δ τ b normal y + R y) ⊆
      tsupport χ ∪ tsupport R := by
  exact (tsupport_add _ R).trans
    (Set.union_subset_union (tsupport_smul_subset_left χ _) Set.Subset.rfl)

/-- For the SAME published primary derivative coefficient, original real/imaginary
amplitude supports imply vanishing outside the original primary support. Cutoff
derivatives are retained in its definition; they cannot enlarge a supported amplitude.
This derives the coefficient-support caller rather than assuming that conclusion. -/
theorem increments_primary_coefficient_of_notMem_support {A : Type*} [Fintype A]
    {n N : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (χ : A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hP : ∀ α, tsupport (P α) ⊆ S) (hQ : ∀ α, tsupport (Q α) ⊆ S)
    (x v : EuclideanSpace ℝ (Fin n)) (hx : x ∉ S) :
    incrementsPrimaryDerivativeCoefficient φ τ χ P Q x v = 0 := by
  have hp (α : A) : x ∉ tsupport (P α) := fun h ↦ hx (hP α h)
  have hq (α : A) : x ∉ tsupport (Q α) := fun h ↦ hx (hQ α h)
  have hp0 (α : A) : P α x = 0 := image_eq_zero_of_notMem_tsupport (hp α)
  have hq0 (α : A) : Q α x = 0 := image_eq_zero_of_notMem_tsupport (hq α)
  have hdp (α : A) : fderiv ℝ (P α) x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) (hp α)
  have hdq (α : A) : fderiv ℝ (Q α) x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) (hq α)
  funext c
  simp [incrementsPrimaryDerivativeCoefficient, hp0, hq0, hdp, hdq]

/-- The actual published primary-wave coefficients obey the ZERO-germ extraction
using only their actual amplitude supports and the ORIGINAL doubled/overlapping-phase
noncriticality. The mode constructor must still supply these amplitude support bounds;
no desired derivative-coefficient support or germ-exclusion conclusion is a premise. -/
theorem increments_primary_four_phase_zero_germ {Λ A I : Type*}
    [Fintype Λ] [Fintype A] {n N : ℕ}
    (φ : Λ → EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ) (hτ : τ ≠ 0)
    (χ : Λ → A → EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : Λ → A → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (S : Λ → Set (EuclideanSpace ℝ (Fin n)))
    (hP : ∀ ν α, tsupport (P ν α) ⊆ S ν)
    (hQ : ∀ ν α, tsupport (Q ν α) ⊆ S ν)
    (x : EuclideanSpace ℝ (Fin n)) (v : I → EuclideanSpace ℝ (Fin n))
    (hdouble : ∀ ν, x ∈ S ν → fderiv ℝ (fun y ↦ φ ν y + φ ν y) x ≠ 0)
    (hinteraction : ∀ ν μ, ν ≠ μ → x ∈ S ν → x ∈ S μ →
      fderiv ℝ (fun y ↦ φ ν y + φ μ y) x ≠ 0 ∧
        fderiv ℝ (fun y ↦ φ ν y - φ μ y) x ≠ 0) (i j : I) :
    let D := fun ν k ↦ incrementsPrimaryDerivativeCoefficient
      (φ ν) τ (χ ν) (P ν) (Q ν) x (v k)
    (∑ ν, ∑ μ, incrementsFourPhaseZeroGermPair (fun ν y ↦ φ ν y / τ) D x ν μ i j) =
      incrementsOppositePrimaryContribution D i j := by
  dsimp only
  simp_rw [increments_four_phase_zero_germ_pair_div φ τ hτ]
  apply increments_four_phase_zero_germ_eq_opposite φ _ S x _ hdouble hinteraction i j
  intro ν hx k
  exact increments_primary_coefficient_of_notMem_support (φ ν) τ (χ ν) (P ν) (Q ν)
    (S ν) (hP ν) (hQ ν) x (v k) hx

end GlobalEmbedding.Paper
