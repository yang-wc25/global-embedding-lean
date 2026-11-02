import GlobalEmbedding.Paper.IncrementsPhaseGermExtraction
import Probes.EvenParameterResponse

/-!
# Reflection parity of the actual zero-phase mean

Source: main.tex, proof of prop:probes after (8.3).
Reflect only the probe labels, leaving the background labels fixed. The full
actual zero-phase coefficient is unchanged, because true phase-germ separation
eliminates cross-label terms and each remaining self-pair is quadratic.
This proof uses the original actual-germ selector; formal labels are not used
as a substitute for nonresonance of the real phase functions.
-/

noncomputable section
open GlobalEmbedding.Paper Filter Set
open scoped Topology ComplexConjugate BigOperators

namespace GlobalEmbedding.Continuation

variable {Λ J X P : Type*} [Fintype Λ] {N : ℕ}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Independent sign reflection of the designated probe labels. -/
def reflectProbeCoefficients (probe : Λ → Bool) (D : Λ → J → Fin N → ℂ) :
    Λ → J → Fin N → ℂ := fun l ↦ if probe l then -D l else D l

/-- Each self-pair retains both conjugate orderings and the original factor 1/4. -/
theorem oppositePrimaryContribution_reflect (probe : Λ → Bool)
    (D : Λ → J → Fin N → ℂ) (i j : J) :
    incrementsOppositePrimaryContribution (reflectProbeCoefficients probe D) i j =
      incrementsOppositePrimaryContribution D i j := by
  unfold incrementsOppositePrimaryContribution
  apply Finset.sum_congr rfl
  intro l _
  cases hl : probe l <;> simp [reflectProbeCoefficients, hl, dotProduct]

/-- Original support and genuine phase noncriticality imply reflection
invariance of the ENTIRE actual zero-germ coefficient. -/
theorem actual_zero_germ_mean_reflect
    (probe : Λ → Bool) (phi : Λ → X → ℝ) (D : Λ → J → Fin N → ℂ)
    (S : Λ → Set X) (x : X)
    (hsupport : ∀ l, x ∉ S l → ∀ i, D l i = 0)
    (hdouble : ∀ l, x ∈ S l → fderiv ℝ (fun y ↦ phi l y + phi l y) x ≠ 0)
    (hinteraction : ∀ l k, l ≠ k → x ∈ S l → x ∈ S k →
      fderiv ℝ (fun y ↦ phi l y + phi k y) x ≠ 0 ∧
        fderiv ℝ (fun y ↦ phi l y - phi k y) x ≠ 0) (i j : J) :
    (∑ l, ∑ k, incrementsFourPhaseZeroGermPair phi
        (reflectProbeCoefficients probe D) x l k i j) =
      ∑ l, ∑ k, incrementsFourPhaseZeroGermPair phi D x l k i j := by
  have hr : ∀ l, x ∉ S l → ∀ i, reflectProbeCoefficients probe D l i = 0 := by
    intro l hl i
    cases hp : probe l <;> simp [reflectProbeCoefficients, hp, hsupport l hl i]
  rw [increments_four_phase_zero_germ_eq_opposite phi _ S x hr hdouble hinteraction,
    increments_four_phase_zero_germ_eq_opposite phi _ S x hsupport hdouble hinteraction,
    oppositePrimaryContribution_reflect]

/-- The actual mean as a function of the real probe parameters. -/
def actualParameterZeroMean (phi : Λ → X → ℝ)
    (D : P → Λ → J → Fin N → ℂ) (x : X) (i j : J) (u : P) : ℂ :=
  ∑ l, ∑ k, incrementsFourPhaseZeroGermPair phi (D u) x l k i j

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The background/odd-probe split is enough for actual parameter evenness.
The hypothesis is a precise coefficient reflection identity, NOT the desired
mean parity or derivative estimate. It is supplied by actual finite-solver
linearity and fixed-background construction. -/
theorem actualParameterZeroMean_even
    (probe : Λ → Bool) (phi : Λ → X → ℝ)
    (D : P → Λ → J → Fin N → ℂ) (S : Λ → Set X) (x : X)
    (hreflect : ∀ u, D (-u) = reflectProbeCoefficients probe (D u))
    (hsupport : ∀ u l, x ∉ S l → ∀ i, D u l i = 0)
    (hdouble : ∀ l, x ∈ S l → fderiv ℝ (fun y ↦ phi l y + phi l y) x ≠ 0)
    (hinteraction : ∀ l k, l ≠ k → x ∈ S l → x ∈ S k →
      fderiv ℝ (fun y ↦ phi l y + phi k y) x ≠ 0 ∧
        fderiv ℝ (fun y ↦ phi l y - phi k y) x ≠ 0) (i j : J) (u : P) :
    actualParameterZeroMean phi D x i j (-u) = actualParameterZeroMean phi D x i j u := by
  unfold actualParameterZeroMean
  rw [hreflect]
  exact actual_zero_germ_mean_reflect probe phi (D u) S x (hsupport u) hdouble hinteraction i j

/-- For the same actual zero-phase coefficient, evenness gives a zero first
parameter derivative at the origin. Differentiability is still a required
regularity input; no invented derivative field or parity of formal labels occurs. -/
theorem fderiv_actualParameterZeroMean_zero
    (probe : Λ → Bool) (phi : Λ → X → ℝ)
    (D : P → Λ → J → Fin N → ℂ) (S : Λ → Set X) (x : X)
    (hreflect : ∀ u, D (-u) = reflectProbeCoefficients probe (D u))
    (hsupport : ∀ u l, x ∉ S l → ∀ i, D u l i = 0)
    (hdouble : ∀ l, x ∈ S l → fderiv ℝ (fun y ↦ phi l y + phi l y) x ≠ 0)
    (hinteraction : ∀ l k, l ≠ k → x ∈ S l → x ∈ S k →
      fderiv ℝ (fun y ↦ phi l y + phi k y) x ≠ 0 ∧
        fderiv ℝ (fun y ↦ phi l y - phi k y) x ≠ 0) (i j : J)
    (hdiff : DifferentiableAt ℝ (actualParameterZeroMean phi D x i j) 0) :
    fderiv ℝ (actualParameterZeroMean phi D x i j) 0 = 0 :=
  fderiv_zero_of_even
    (actualParameterZeroMean_even probe phi D S x hreflect hsupport hdouble hinteraction i j) hdiff

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_zero_germ_mean_reflect
#print axioms GlobalEmbedding.Continuation.actualParameterZeroMean_even
#print axioms GlobalEmbedding.Continuation.fderiv_actualParameterZeroMean_zero
