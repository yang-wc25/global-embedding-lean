import GlobalEmbedding.Paper.IncrementsPhaseGermExtraction
import GlobalEmbedding.Paper.IncrementsMeanQuadraticRemainder
import GlobalEmbedding.Paper.IncrementsSecondaryMode
import Mathlib.Data.Fin.VecNotation

/-!
# Actual negative nonzero quadratic forcing for the original secondary modes

Source: original `lem:increments`, main.tex638–673.
DAG: `increments-nonzero-quadratic-forcing-consumer`, exclusive W4.
STAGE2 ONLY: coherent actual definitions and two named holes awaiting ROOT lock.
Actual primary coefficient producers and secondary-chart transport remain callers.
No generic phase-packing, complex product library or second mode solver is introduced.
-/

noncomputable section
open Filter Set
open scoped ContDiff Topology ComplexConjugate
namespace GlobalEmbedding.Paper

variable {m N : ℕ} {Λ A Ep : Type*} [Fintype A]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Slots" => Fin (m + 1)

/-- The literal grouped physical derivative coefficient, with the actual finite
subordinate sum, cutoff derivatives and fast derivative retained. This only
evaluates the accepted primary coefficient on the original parameter slice and
physical directions. Source: original main.tex638–655. -/
def incrementsSecondaryPhysicalCoefficient
    (phi : Λ → Ep → D → ℝ) (tau : ℝ) (chi : Λ → Ep → A → D → ℝ)
    (P Q : Λ → Ep → A → D → V) (v : Slots → X → D)
    (z : X) (nu : Λ) (i : Slots) : Fin N → ℂ :=
  incrementsPrimaryDerivativeCoefficient (phi nu z.1) tau (chi nu z.1)
    (P nu z.1) (Q nu z.1) z.2 (v i z)

/-- The four actual signed phase functions, in exactly the canonical expansion's
order. No half-list, quotient or formal frequency substitutes for these values.
Source: original main.tex645–668 and canonical four-phase expansion. -/
def incrementsSecondaryQuadraticPhase (phi : Λ → Ep → D → ℝ)
    (nu mu : Λ) (q : Fin 4) (z : X) : ℝ :=
  ![phi nu z.1 z.2 + phi mu z.1 z.2,
    phi nu z.1 z.2 - phi mu z.1 z.2,
    -phi nu z.1 z.2 + phi mu z.1 z.2,
    -phi nu z.1 z.2 - phi mu z.1 z.2] q

/-- The actual NEGATIVE symmetric forcing for one ordered pair and one signed
branch. Original quarter times the explicit symmetric average is one eighth.
RAW physical coefficients already contain delta; no extra delta squared occurs.
Conjugations are explicit and the dot products are complex-bilinear. Both real
and imaginary forcing channels are the corresponding parts of this same negative
coefficient. Source: original nonzero quadratic cancellation, main.tex668–673. -/
def incrementsSecondaryQuadraticForcing
    (phi : Λ → Ep → D → ℝ) (tau : ℝ) (chi : Λ → Ep → A → D → ℝ)
    (P Q : Λ → Ep → A → D → V) (v : Slots → X → D)
    (nu mu : Λ) (q : Fin 4) (z : X) (i j : Slots) : ℂ :=
  let d := incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z
  let b := fun a b : Slots ↦
    ![d nu a ⬝ᵥ d mu b,
      d nu a ⬝ᵥ (fun c ↦ conj (d mu b c)),
      (fun c ↦ conj (d nu a c)) ⬝ᵥ d mu b,
      (fun c ↦ conj (d nu a c)) ⬝ᵥ (fun c ↦ conj (d mu b c))] q
  show ℂ from -(1 / 8 : ℂ) * (b i j + b j i)

/-- The FULL conjugate-closed, ordered finite sum of the actual negative forcing
is exactly minus the nonzero quadratic part of the SAME literal physical wave.
Only the identically zero diagonal opposite-sign records are omitted. Actual
noncritical/support data classify the other records as nonconstant phase germs
using the already accepted phase-germ provider, not this algebraic identity.

Natural-language proof: apply the accepted grouped physical derivative theorem
at the two original directions. Apply its accepted four-phase Euclidean pairing
expansion at slots (i,j) and (j,i). Symmetrize these equalities; symmetry of the
real inner product leaves their left side unchanged. The symmetrized coefficient
is exactly the negative one-eighth definition above. The excluded equal-label
opposite-sign records have phase zero and sum to the canonical opposite-primary
contribution. That contribution is symmetric by native dotProduct commutation,
so its symmetric average is unchanged. Finite sums and real parts then give the
stated negative identity. No individual ordered product is assumed symmetric;
all four branches and all ordered labels remain. There is no extra half factor,
delta factor, new phase expansion or mode-reconstruction proof. Source:
original main.tex645–668. -/
theorem increments_secondary_quadratic_forcing_exact [Fintype Λ] [DecidableEq Λ]
    (phi : Λ → Ep → D → ℝ) (tau : ℝ) (chi : Λ → Ep → A → D → ℝ)
    (P Q : Λ → Ep → A → D → V) (v : Slots → X → D) (z : X)
    (hphi : ∀ nu, DifferentiableAt ℝ (phi nu z.1) z.2)
    (hchi : ∀ nu a, DifferentiableAt ℝ (chi nu z.1 a) z.2)
    (hP : ∀ nu a, DifferentiableAt ℝ (P nu z.1 a) z.2)
    (hQ : ∀ nu a, DifferentiableAt ℝ (Q nu z.1 a) z.2) (i j : Slots) :
    let wave := incrementsPrimaryWave (fun nu ↦ phi nu z.1) tau
      (fun nu ↦ chi nu z.1) (fun nu ↦ P nu z.1) (fun nu ↦ Q nu z.1)
    let coeff := incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z
    (∑ nu, ∑ mu, ∑ q ∈ (Finset.univ.filter
      (fun q : Fin 4 ↦ nu ≠ mu ∨ q = 0 ∨ q = 3)),
      (incrementsMeanPhase (incrementsSecondaryQuadraticPhase phi nu mu q z / tau) *
        incrementsSecondaryQuadraticForcing phi tau chi P Q v nu mu q z i j).re) =
      -inner ℝ (fderiv ℝ wave z.2 (v i z)) (fderiv ℝ wave z.2 (v j z)) +
        (incrementsOppositePrimaryContribution coeff i j).re := by
  intro wave coeff
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
  have hd (a : Slots) : fderiv ℝ wave z.2 (v a z) =
      incrementsGroupedRealDerivative theta coeff a := by
    exact increments_primary_wave_grouped_derivative (fun nu ↦ phi nu z.1) tau
      (fun nu ↦ chi nu z.1) (fun nu ↦ P nu z.1) (fun nu ↦ Q nu z.1)
      z.2 (v a z) hphi hchi hP hQ
  rw [hd i, hd j]
  have hr := congrArg Complex.re hsum
  simpa only [term, Complex.re_sum, Complex.add_re, Complex.neg_re, Complex.ofReal_re] using hr

/-- The actual negative forcing is symmetric, jointly smooth, supported in the
actual primary pair intersection, and has delta-squared SIZE from the SAME-order
RAW physical derivative jets. No desired forcing bound or regularity is an input.
The constant is chosen before every label type, subordinate count, direction
family, scale and field; it has no global primary-mode count.

Natural-language proof: evaluate only the two actual grouped coefficient fields
nu and mu. Native coordinate projections and complex conjugation preserve their
smoothness and bound their jets by the genuine input jets. Each of the four branch
products is a finite coordinate sum. Apply existing native multiplication/CLM
weighted jet bounds at the SAME order and sum over ambient coordinates; do not
reprove the binomial estimate or introduce a generic complex bilinear library.
Multiplication yields two factors of abs(delta), hence delta squared. The actual
symmetric average and quarter give the displayed negative forcing and its real
channels; retain native channel norms in the chosen constant. No global label
sum occurs in this bound. Native support of multiplication, zero-preserving
conjugation, finite sums and coordinate projection gives intersection of the two
actual coefficient tsupports, which are closed. The definition is symmetric in
i,j. Actual computation/smooth jets/support of the primary coefficients and
secondary adapted-chart observation transport remain genuine caller obligations;
no full U2 or original target conclusion is claimed. Source: main.tex668–673. -/
theorem increments_secondary_quadratic_forcing_data
    (n : ℕ) (N0 : ℕ) (M0 : ℝ) (hM0 : 0 ≤ M0) :
    ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ {m0 : ℕ} {Param Label Sub : Type*} [Fintype Sub]
        [NormedAddCommGroup Param] [NormedSpace ℝ Param]
        (phi : Label → Param → EuclideanSpace ℝ (Fin (m0 + 1)) → ℝ)
        (tau : ℝ) (chi : Label → Param → Sub → EuclideanSpace ℝ (Fin (m0 + 1)) → ℝ)
        (P Q : Label → Param → Sub → EuclideanSpace ℝ (Fin (m0 + 1)) →
          EuclideanSpace ℝ (Fin N0))
        (v : Fin (m0 + 1) → (Param × EuclideanSpace ℝ (Fin (m0 + 1))) →
          EuclideanSpace ℝ (Fin (m0 + 1)))
        (nu mu : Label) (q : Fin 4)
        (O S : Set (Param × EuclideanSpace ℝ (Fin (m0 + 1))))
        (hO : IsOpen O) (hSO : S ⊆ O) (ell delta : ℝ) (hell : 0 < ell)
        (hnu : ContDiffOn ℝ ∞
          (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z nu) O)
        (hmu : ContDiffOn ℝ ∞
          (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z mu) O)
        (hnub : ∀ r ≤ n, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
          (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z nu) x‖ ≤
            M0 * |delta|)
        (hmub : ∀ r ≤ n, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
          (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z mu) x‖ ≤
            M0 * |delta|),
      let h := incrementsSecondaryQuadraticForcing phi tau chi P Q v nu mu q
      let hR := fun z i j ↦ (h z i j).re
      let hI := fun z i j ↦ (h z i j).im
      ContDiffOn ℝ ∞ hR O ∧ ContDiffOn ℝ ∞ hI O ∧
      (∀ z i j, h z i j = h z j i) ∧
      (tsupport hR ⊆
        tsupport (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z nu) ∩
        tsupport (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z mu)) ∧
      (tsupport hI ⊆
        tsupport (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z nu) ∩
        tsupport (fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z mu)) ∧
      (∀ r ≤ n, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r hR x‖ ≤ CH * delta ^ 2) ∧
      (∀ r ≤ n, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r hI x‖ ≤ CH * delta ^ 2) := by
  classical
  let Cb : ℝ := 2 * N0
  let Cc : ℝ := max ‖Complex.reCLM‖ ‖Complex.imCLM‖
  refine ⟨Cc * 2 ^ n * Cb * M0 ^ 2, by dsimp [Cc, Cb]; positivity, ?_⟩
  intro m0 Param Label Sub _ _ _ phi tau chi P Q v nu mu q O S hO hSO
    ell delta hell hnu hmu hnub hmub h hR hI
  let Arr := Fin (m0 + 1) → Fin N0 → ℂ
  let Out := Fin (m0 + 1) → Fin (m0 + 1) → ℂ
  let dnu : (Param × EuclideanSpace ℝ (Fin (m0 + 1))) → Arr :=
    fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z nu
  let dmu : (Param × EuclideanSpace ℝ (Fin (m0 + 1))) → Arr :=
    fun z ↦ incrementsSecondaryPhysicalCoefficient phi tau chi P Q v z mu
  let cj : Arr →L[ℝ] Arr :=
    (ContinuousLinearEquiv.piCongrRight fun _i : Fin (m0 + 1) ↦
      ContinuousLinearEquiv.piCongrRight fun _c : Fin N0 ↦ Complex.conjCLE).toContinuousLinearMap
  have hcj : ‖cj‖ ≤ 1 := by
    apply cj.opNorm_le_bound zero_le_one
    intro a
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
    intro c
    change ‖conj (a i c)‖ ≤ ‖a‖
    rw [Complex.norm_conj]
    exact (norm_le_pi_norm (a i) c).trans (norm_le_pi_norm a i)
  let f := ![dnu, dnu, cj ∘ dnu, cj ∘ dnu] q
  let g := ![dmu, cj ∘ dmu, dmu, cj ∘ dmu] q
  have hf : ContDiffOn ℝ ∞ f O := by
    fin_cases q
    · exact hnu
    · exact hnu
    · exact cj.contDiff.comp_contDiffOn hnu
    · exact cj.contDiff.comp_contDiffOn hnu
  have hg : ContDiffOn ℝ ∞ g O := by
    fin_cases q
    · exact hmu
    · exact cj.contDiff.comp_contDiffOn hmu
    · exact hmu
    · exact cj.contDiff.comp_contDiffOn hmu
  have hconjb (d : (Param × EuclideanSpace ℝ (Fin (m0 + 1))) → Arr)
      (hd : ContDiffOn ℝ ∞ d O) (r : ℕ) (x : Param × EuclideanSpace ℝ (Fin (m0 + 1)))
      (hx : x ∈ S) (hb : ell ^ r * ‖iteratedFDeriv ℝ r d x‖ ≤ M0 * |delta|) :
      ell ^ r * ‖iteratedFDeriv ℝ r (cj ∘ d) x‖ ≤ M0 * |delta| := by
    calc
      _ ≤ ell ^ r * (‖cj‖ * ‖iteratedFDeriv ℝ r d x‖) :=
        mul_le_mul_of_nonneg_left (cj.norm_iteratedFDeriv_comp_left
          (hd.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
      _ ≤ ell ^ r * (1 * ‖iteratedFDeriv ℝ r d x‖) := by gcongr
      _ ≤ _ := by simpa using hb
  have hfb : ∀ r ≤ n, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r f x‖ ≤ M0 * |delta| := by
    intro r hr x hx
    fin_cases q
    · exact hnub r hr x hx
    · exact hnub r hr x hx
    · exact hconjb dnu hnu r x hx (hnub r hr x hx)
    · exact hconjb dnu hnu r x hx (hnub r hr x hx)
  have hgb : ∀ r ≤ n, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r g x‖ ≤ M0 * |delta| := by
    intro r hr x hx
    fin_cases q
    · exact hmub r hr x hx
    · exact hconjb dmu hmu r x hx (hmub r hr x hx)
    · exact hmub r hr x hx
    · exact hconjb dmu hmu r x hx (hmub r hr x hx)
  let beta : Arr →ₗ[ℝ] Arr →ₗ[ℝ] Out := LinearMap.mk₂ ℝ
    (fun a b i j ↦ -(1 / 8 : ℂ) * (a i ⬝ᵥ b j + a j ⬝ᵥ b i))
    (by
      intro a a' b
      funext i j
      change -(1 / 8 : ℂ) * ((a i + a' i) ⬝ᵥ b j + (a j + a' j) ⬝ᵥ b i) =
        -(1 / 8 : ℂ) * (a i ⬝ᵥ b j + a j ⬝ᵥ b i) +
          -(1 / 8 : ℂ) * (a' i ⬝ᵥ b j + a' j ⬝ᵥ b i)
      simp only [add_dotProduct]
      ring)
    (by
      intro r a b
      funext i j
      change -(1 / 8 : ℂ) * ((r • a i) ⬝ᵥ b j + (r • a j) ⬝ᵥ b i) =
        r • (-(1 / 8 : ℂ) * (a i ⬝ᵥ b j + a j ⬝ᵥ b i))
      rw [smul_dotProduct, smul_dotProduct]
      simp only [Algebra.smul_def]
      ring)
    (by
      intro a b b'
      funext i j
      change -(1 / 8 : ℂ) * (a i ⬝ᵥ (b j + b' j) + a j ⬝ᵥ (b i + b' i)) =
        -(1 / 8 : ℂ) * (a i ⬝ᵥ b j + a j ⬝ᵥ b i) +
          -(1 / 8 : ℂ) * (a i ⬝ᵥ b' j + a j ⬝ᵥ b' i)
      simp only [dotProduct_add]
      ring)
    (by
      intro r a b
      funext i j
      change -(1 / 8 : ℂ) * (a i ⬝ᵥ (r • b j) + a j ⬝ᵥ (r • b i)) =
        r • (-(1 / 8 : ℂ) * (a i ⬝ᵥ b j + a j ⬝ᵥ b i))
      rw [dotProduct_smul, dotProduct_smul]
      simp only [Algebra.smul_def]
      ring)
  have hdot (a b : Arr) (i j : Fin (m0 + 1)) :
      ‖a i ⬝ᵥ b j‖ ≤ N0 * ‖a‖ * ‖b‖ := by
    calc
      _ ≤ ∑ c : Fin N0, ‖a i c * b j c‖ := norm_sum_le _ _
      _ ≤ ∑ _c : Fin N0, ‖a‖ * ‖b‖ := by
        apply Finset.sum_le_sum
        intro c hc
        exact (norm_mul_le _ _).trans (mul_le_mul
          ((norm_le_pi_norm (a i) c).trans (norm_le_pi_norm a i))
          ((norm_le_pi_norm (b j) c).trans (norm_le_pi_norm b j))
          (norm_nonneg _) (norm_nonneg _))
      _ = _ := by simp; ring
  have hbeta (a b : Arr) : ‖beta a b‖ ≤ Cb * ‖a‖ * ‖b‖ := by
    apply (pi_norm_le_iff_of_nonneg (by dsimp [Cb]; positivity)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by dsimp [Cb]; positivity)).mpr
    intro j
    change ‖-(1 / 8 : ℂ) * (a i ⬝ᵥ b j + a j ⬝ᵥ b i)‖ ≤ _
    calc
      _ ≤ ‖-(1 / 8 : ℂ)‖ * (‖a i ⬝ᵥ b j‖ + ‖a j ⬝ᵥ b i‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
      _ ≤ 1 * (N0 * ‖a‖ * ‖b‖ + N0 * ‖a‖ * ‖b‖) := by
        gcongr
        · norm_num
        · exact hdot a b i j
        · exact hdot a b j i
      _ = _ := by dsimp [Cb]; ring
  let B : Arr →L[ℝ] Arr →L[ℝ] Out := beta.mkContinuous₂ Cb hbeta
  have hBnorm : ‖B‖ ≤ Cb := beta.mkContinuous₂_norm_le (by dsimp [Cb]; positivity) hbeta
  have heq : h = (fun z ↦ B (f z) (g z)) := by
    funext z i j
    fin_cases q <;> rfl
  have hh : ContDiffOn ℝ ∞ h O := by
    rw [heq]
    exact (B.contDiff.comp_contDiffOn hf).clm_apply hg
  let channel := fun (c : ℂ →L[ℝ] ℝ) ↦
    ContinuousLinearMap.pi fun i : Fin (m0 + 1) ↦ ContinuousLinearMap.pi
      fun j : Fin (m0 + 1) ↦ c.comp ((ContinuousLinearMap.proj j :
        (Fin (m0 + 1) → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj i : Out →L[ℝ] (Fin (m0 + 1) → ℂ)))
  have hchannel (c : ℂ →L[ℝ] ℝ) : ‖channel c‖ ≤ ‖c‖ := by
    apply (channel c).opNorm_le_bound (norm_nonneg c)
    intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    change ‖c (a i j)‖ ≤ ‖c‖ * ‖a‖
    exact (c.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_le_pi_norm (a i) j).trans (norm_le_pi_norm a i)) (norm_nonneg _))
  have hR_eq : hR = channel Complex.reCLM ∘ h := rfl
  have hI_eq : hI = channel Complex.imCLM ∘ h := rfl
  have hzero_nu (x : Param × EuclideanSpace ℝ (Fin (m0 + 1))) (hx : dnu x = 0) :
      h x = 0 := by
    have hfx : f x = 0 := by fin_cases q <;> simp [f, Function.comp_apply, hx]
    rw [heq]
    change B (f x) (g x) = 0
    rw [hfx]
    simp
  have hzero_mu (x : Param × EuclideanSpace ℝ (Fin (m0 + 1))) (hx : dmu x = 0) :
      h x = 0 := by
    have hgx : g x = 0 := by fin_cases q <;> simp [g, Function.comp_apply, hx]
    rw [heq]
    change B (f x) (g x) = 0
    rw [hgx]
    simp
  have hsup : tsupport h ⊆ tsupport dnu ∩ tsupport dmu := by
    apply closure_minimal _ ((isClosed_tsupport dnu).inter (isClosed_tsupport dmu))
    intro x hx
    constructor
    · by_contra hn
      exact hx (hzero_nu x (image_eq_zero_of_notMem_tsupport hn))
    · by_contra hm
      exact hx (hzero_mu x (image_eq_zero_of_notMem_tsupport hm))
  have hhb : ∀ r ≤ n, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r h x‖ ≤
      2 ^ n * Cb * M0 ^ 2 * delta ^ 2 := by
    intro r hr x hx
    have hbf : ContDiffOn ℝ ∞ (B ∘ f) O := B.contDiff.comp_contDiffOn hf
    have hab (i : ℕ) (hi : i ≤ r) : ell ^ i * ‖iteratedFDeriv ℝ i (B ∘ f) x‖ ≤
        Cb * (M0 * |delta|) := by
      calc
        _ ≤ ell ^ i * (‖B‖ * ‖iteratedFDeriv ℝ i f x‖) :=
          mul_le_mul_of_nonneg_left (B.norm_iteratedFDeriv_comp_left
            (hf.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
        _ ≤ ell ^ i * (Cb * ‖iteratedFDeriv ℝ i f x‖) := by gcongr
        _ = Cb * (ell ^ i * ‖iteratedFDeriv ℝ i f x‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hfb i (hi.trans hr) x hx)
          (by dsimp [Cb]; positivity)
    have hp := scaled_clm_apply O hO (B ∘ f) g hbf hg r 0 ell
      (Cb * (M0 * |delta|)) (M0 * |delta|) hell.le hab
      (fun i hi ↦ by simpa using hgb i (hi.trans hr) x hx) (hSO hx)
    rw [heq]
    calc
      _ ≤ 2 ^ r * (Cb * (M0 * |delta|)) * (M0 * |delta|) := by simpa using hp
      _ ≤ 2 ^ n * (Cb * (M0 * |delta|)) * (M0 * |delta|) := by
        dsimp [Cb]
        gcongr
        norm_num
      _ = _ := by rw [← sq_abs delta]; ring
  have hcb (c : ℂ →L[ℝ] ℝ) (hc : ‖c‖ ≤ Cc) (r : ℕ) (hr : r ≤ n)
      (x : Param × EuclideanSpace ℝ (Fin (m0 + 1))) (hx : x ∈ S) :
      ell ^ r * ‖iteratedFDeriv ℝ r (channel c ∘ h) x‖ ≤
        (Cc * 2 ^ n * Cb * M0 ^ 2) * delta ^ 2 := by
    calc
      _ ≤ ell ^ r * (‖channel c‖ * ‖iteratedFDeriv ℝ r h x‖) :=
        mul_le_mul_of_nonneg_left ((channel c).norm_iteratedFDeriv_comp_left
          (hh.contDiffAt (hO.mem_nhds (hSO hx))) (by simp)) (by positivity)
      _ ≤ ell ^ r * (Cc * ‖iteratedFDeriv ℝ r h x‖) := by
        gcongr
        exact (hchannel c).trans hc
      _ = Cc * (ell ^ r * ‖iteratedFDeriv ℝ r h x‖) := by ring
      _ ≤ Cc * (2 ^ n * Cb * M0 ^ 2 * delta ^ 2) :=
        mul_le_mul_of_nonneg_left (hhb r hr x hx) (by dsimp [Cc]; positivity)
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR_eq]
    exact (channel Complex.reCLM).contDiff.comp_contDiffOn hh
  · rw [hI_eq]
    exact (channel Complex.imCLM).contDiff.comp_contDiffOn hh
  · intro x i j
    dsimp [h, incrementsSecondaryQuadraticForcing]
    rw [add_comm]
  · rw [hR_eq]
    exact (tsupport_comp_subset (map_zero _) h).trans hsup
  · rw [hI_eq]
    exact (tsupport_comp_subset (map_zero _) h).trans hsup
  · intro r hr x hx
    rw [hR_eq]
    exact hcb Complex.reCLM (le_max_left _ _) r hr x hx
  · intro r hr x hx
    rw [hI_eq]
    exact hcb Complex.imCLM (le_max_right _ _) r hr x hx

end GlobalEmbedding.Paper
