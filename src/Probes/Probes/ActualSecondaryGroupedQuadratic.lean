import GlobalEmbedding.Paper.IncrementsSecondaryQuadraticForcing

/-! The actual signed quadratic forcing is purely algebraic in the actual
physical coefficients. This form avoids imposing differentiability on phases
outside their genuine primary domains. Original global-wave derivative bindings
can be inserted afterwards, where inactive labels are handled by zero germs. -/

noncomputable section
open Filter Set
open scoped ContDiff Topology ComplexConjugate
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {m N : ℕ} {Λ A Ep : Type*} [Fintype A]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Slots" => Fin (m + 1)

theorem actual_secondary_quadratic_grouped_identity [Fintype Λ] [DecidableEq Λ]
    (phi : Λ → Ep → D → ℝ) (tau : ℝ) (chi : Λ → Ep → A → D → ℝ)
    (P Q : Λ → Ep → A → D → V) (v : Slots → X → D) (z : X) (i j : Slots) :
    let coeff := incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z
    let theta := fun nu => phi nu z.1 z.2 / tau
    (∑ nu, ∑ mu, ∑ q ∈ (Finset.univ.filter
      (fun q : Fin 4 ↦ nu ≠ mu ∨ q = 0 ∨ q = 3)),
      (incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi nu mu q z / tau) *
        incrementsSecondaryQuadraticForcing phi tau chi P Q v nu mu q z i j).re) =
      -inner ℝ (incrementsGroupedRealDerivative theta coeff i)
        (incrementsGroupedRealDerivative theta coeff j) +
        (incrementsOppositePrimaryContribution coeff i j).re := by
  intro coeff
  let theta := fun nu ↦ phi nu z.1 z.2 / tau
  let b := fun nu mu (q : Fin 4) (a b : Slots) ↦
    ![coeff nu a ⬝ᵥ coeff mu b,
      coeff nu a ⬝ᵥ (fun c ↦ conj (coeff mu b c)),
      (fun c ↦ conj (coeff nu a c)) ⬝ᵥ coeff mu b,
      (fun c ↦ conj (coeff nu a c)) ⬝ᵥ (fun c ↦ conj (coeff mu b c))] q
  let phase := fun nu mu (q : Fin 4) ↦
    ![incrementsMeanPhase (theta nu + theta mu),
      incrementsMeanPhase (theta nu - theta mu),
      incrementsMeanPhase (-theta nu + theta mu),
      incrementsMeanPhase (-theta nu - theta mu)] q
  let t := fun nu mu a b ↦ (1 / 4 : ℂ) *
    (phase nu mu 0 * (coeff nu a ⬝ᵥ coeff mu b) +
      phase nu mu 1 * (coeff nu a ⬝ᵥ (fun c ↦ conj (coeff mu b c))) +
      phase nu mu 2 * ((fun c ↦ conj (coeff nu a c)) ⬝ᵥ coeff mu b) +
      phase nu mu 3 * ((fun c ↦ conj (coeff nu a c)) ⬝ᵥ
        (fun c ↦ conj (coeff mu b c))))
  let opp := fun nu ↦ (1 / 4 : ℂ) *
    ((coeff nu i ⬝ᵥ (fun c ↦ conj (coeff nu j c))) +
      ((fun c ↦ conj (coeff nu i c)) ⬝ᵥ coeff nu j))
  have hp0 : incrementsMeanPhase 0 = 1 := by simp [incrementsMeanPhase]
  have hp (nu mu : Λ) (q : Fin 4) :
      incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi nu mu q z / tau) =
        phase nu mu q := by
    fin_cases q <;> simp [incrementsSecondaryQuadraticPhase, phase, theta,
      add_div, sub_div, neg_div]
  have hf (nu mu : Λ) (q : Fin 4) (a b' : Slots) :
      incrementsSecondaryQuadraticForcing phi tau chi P Q v nu mu q z a b' =
        -(1 / 8 : ℂ) * (b nu mu q a b' + b nu mu q b' a) := rfl
  let term := fun nu mu ↦ ∑ q ∈ (Finset.univ.filter
    (fun q : Fin 4 ↦ nu ≠ mu ∨ q = 0 ∨ q = 3)),
      incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi nu mu q z / tau) *
        incrementsSecondaryQuadraticForcing phi tau chi P Q v nu mu q z i j
  have hpair (nu mu : Λ) : term nu mu =
      -(t nu mu i j + t nu mu j i) / 2 + if nu = mu then opp nu else 0 := by
    dsimp only [term]
    simp_rw [hp, hf]
    by_cases hnm : nu = mu
    · subst mu
      simp [Finset.sum_filter, Fin.sum_univ_succ, b, t, phase, opp, hp0]
      simp only [dotProduct_comm]
      ring
    · simp [Fin.sum_univ_succ, hnm, b, t, phase]
      ring
  have hquad (a b' : Slots) :
      (inner ℝ (incrementsGroupedRealDerivative theta coeff a)
        (incrementsGroupedRealDerivative theta coeff b') : ℂ) = ∑ nu, ∑ mu, t nu mu a b' :=
    increments_grouped_quadratic_four_phases theta coeff a b'
  have hsum : (∑ nu, ∑ mu, term nu mu) =
      -(inner ℝ (incrementsGroupedRealDerivative theta coeff i)
        (incrementsGroupedRealDerivative theta coeff j) : ℂ) +
        incrementsOppositePrimaryContribution coeff i j := by
    simp_rw [hpair]
    simp only [neg_add_rev, neg_div, add_div, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [← Finset.sum_div]
    rw [← hquad i j, ← hquad j i, real_inner_comm]
    change _ = _ + ∑ nu, opp nu
    ring
  have hr := congrArg Complex.re hsum
  simpa only [term, Complex.re_sum, Complex.add_re, Complex.neg_re, Complex.ofReal_re] using hr

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_quadratic_grouped_identity
