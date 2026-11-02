import GlobalEmbedding.Paper.CollarGoursatAnalyticMajorant
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Topology ContDiff
open Filter Set

/-!
# A jointly analytic Goursat PDE majorant with nonnegative coordinate Taylor coefficients

Source: Gantumur, Math580 notes2, Theorem18 proof, equations47–51.
-/

namespace GlobalEmbedding.Paper

private theorem linearPullbackDerivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → ℝ} (hv : AnalyticAt ℝ v 0) (L : E →L[ℝ] ℝ)
    (k : ℕ) (h : Fin k → E) :
    iteratedFDeriv ℝ k (v ∘ L) 0 h =
      iteratedDeriv k v 0 * ∏ i, L (h i) := by
  obtain ⟨r, hr, hvr⟩ := Metric.eventually_nhds_iff_ball.mp hv.eventually_analyticAt
  have hvon : ContDiffOn ℝ ∞ v (Metric.ball 0 r) :=
    fun t ht ↦ (hvr t ht).contDiffAt.contDiffWithinAt
  have hopen : IsOpen (L ⁻¹' Metric.ball 0 r) := Metric.isOpen_ball.preimage L.continuous
  have h0 : (0 : E) ∈ L ⁻¹' Metric.ball 0 r := by
    simpa only [mem_preimage, map_zero] using Metric.mem_ball_self hr
  have heq := L.iteratedFDerivWithin_comp_right hvon Metric.isOpen_ball.uniqueDiffOn
    hopen.uniqueDiffOn h0 (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hopen h0,
    iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball (show L 0 ∈ Metric.ball 0 r from h0)]
    at heq
  rw [heq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  exact mul_comm _ _

private noncomputable def goursatLinear {n : ℕ} (ρ : ℝ) :
    (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ where
  toFun z := z.1 + ρ * ∑ i, z.2 i
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply,
    Finset.sum_add_distrib]; ring
  map_smul' c z := by
    change c * z.1 + ρ * (∑ i, c * z.2 i) = c * (z.1 + ρ * ∑ i, z.2 i)
    rw [← Finset.mul_sum]
    ring
  cont := by fun_prop

private theorem chooseRho (n m M R : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ (n * m * ρ / R) * M < 1 := by
  let q := n * m * M / R
  have hq : 0 ≤ q := div_nonneg (mul_nonneg (mul_nonneg hn hm) hM) hR.le
  let ρ := 1 / (2 * (q + 1))
  have hd : 0 < 2 * (q + 1) := by positivity
  have hρ : 0 < ρ := one_div_pos.mpr hd
  refine ⟨ρ, hρ, (div_le_one hd).mpr (by linarith), ?_⟩
  have heq : (n * m * ρ / R) * M = q / (2 * (q + 1)) := by
    dsimp [q, ρ]
    ring
  rw [heq]
  exact (div_lt_one hd).mpr (by linarith)

private theorem multivariateOfScalar {n m : ℕ} (M R ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → ℝ) (hv0 : v 0 = 0) (hva : AnalyticAt ℝ v 0)
    (hvd0 : deriv v 0 = 0)
    (heq : ∀ᶠ t in 𝓝 0, deriv v t =
      M / ((1 - (t / ρ + (m : ℝ) * v t) / R) *
        (1 - ((n : ℝ) * m * ρ / R) * deriv v t)) - M)
    (hpos : ∀ k, 0 ≤ iteratedDeriv k v 0) :
    ∃ U : (ℝ × EuclideanSpace ℝ (Fin n)) → ℝ,
      U 0 = 0 ∧ AnalyticAt ℝ U 0 ∧ fderiv ℝ U 0 = 0 ∧
      (∀ᶠ z in 𝓝 0, fderiv ℝ U z (1, 0) =
        M / ((1 - ((∑ i, z.2 i) + z.1 / ρ + (m : ℝ) * U z) / R) *
          (1 - (∑ i : Fin n, ∑ _j : Fin m,
            fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R)) - M) ∧
      (∀ k (h : Fin k → ℝ × EuclideanSpace ℝ (Fin n)),
        (∀ i, 0 ≤ (h i).1 ∧ ∀ j, 0 ≤ (h i).2 j) →
        0 ≤ iteratedFDeriv ℝ k U 0 h) := by
  let L := goursatLinear (n := n) ρ
  let U := v ∘ L
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by
    have ht : Tendsto L (𝓝 0) (𝓝 (L 0)) := L.continuous.continuousAt
    simpa only [map_zero] using ht
  have hderiv : ∀ᶠ z in 𝓝 0, fderiv ℝ U z = (deriv v (L z)) • L := by
    filter_upwards [hL.eventually hva.eventually_analyticAt] with z hz
    exact (hz.differentiableAt.hasDerivAt.comp_hasFDerivAt z L.hasFDerivAt).fderiv
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [U, Function.comp_apply, map_zero] using hv0
  · have hvL : AnalyticAt ℝ v (L 0) := by simpa only [map_zero] using hva
    exact hvL.comp (L.analyticAt 0)
  · simpa only [map_zero, hvd0, zero_smul] using hderiv.self_of_nhds
  · filter_upwards [hderiv, hL.eventually heq] with z hz hzeq
    have htime : L (1, 0) = 1 := by simp [L, goursatLinear]
    have hspace (i : Fin n) : L (0, EuclideanSpace.single i 1) = ρ := by
      simp [L, goursatLinear, EuclideanSpace.single]
    simp only [hz, _root_.smul_apply, smul_eq_mul, htime, mul_one, hspace]
    have hfirst : (L z / ρ + (m : ℝ) * v (L z)) =
        (∑ i, z.2 i) + z.1 / ρ + (m : ℝ) * U z := by
      dsimp [L, goursatLinear, U]
      field_simp [hρ.ne']
      ring
    have hsecond : (∑ i : Fin n, ∑ _j : Fin m, deriv v (L z) * ρ) / R =
        ((n : ℝ) * m * ρ / R) * deriv v (L z) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsecond, ← hfirst]
    exact hzeq
  · intro k h hh
    rw [linearPullbackDerivatives hva L]
    apply mul_nonneg (hpos k) (Finset.prod_nonneg fun i _ ↦ ?_)
    change 0 ≤ (h i).1 + ρ * ∑ j, (h i).2 j
    exact add_nonneg (hh i).1 (mul_nonneg hρ.le (Finset.sum_nonneg fun j _ ↦ (hh i).2 j))

/-- Construct the actual convergent symmetric PDE majorant from Gantumur's scalar ODE.

Source: Gantumur, notes2, Theorem18 proof, equations47–51 (printed pp9–10).
For n spatial coordinates and m>0 components, choose an actual 0<ρ≤1 and return the common
component U(t,x)=v(t+ρ∑xᵢ) of the symmetric m-component majorant. It is jointly real analytic,
vanishes to first order at0, and satisfies the actual rational majorant PDE near0. All actual
iterated Frechet derivatives at0 are nonnegative on coordinatewise nonnegative directions;
in particular all coordinate Taylor coefficients are nonnegative. The zero-spatial-dimensional
case and M=0 are included.

Proof: choose ρ=1/(2(q+1)), q=nmM/R≥0. This makes a=nmρ/R nonnegative and aM<1.
The proved analytic scalar Goursat majorant supplies v with nonnegative derivatives. Compose
v with the actual continuous linear map L(t,x)=t+ρ∑xᵢ. The actual Frechet chain rule gives
the time derivative v′(Lz) and each spatial derivative ρv′(Lz). Their finite sums reduce the
rational PDE exactly to the scalar equation. On a genuine open neighborhood v is smooth;
the native iterated derivative formula for linear precomposition and open-set derivative
conversion give DᵏU(0)[hᵢ]=v⁽ᵏ⁾(0)∏L(hᵢ). Both factors are nonnegative on nonnegative
coordinate directions. No unknown original-PDE coefficients or convergence are assumed.
Coefficient domination for the original PDE remains a separate obligation. -/
theorem collarGoursatPDEMajorant (n m : ℕ) (hm : 0 < m)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∃ U : (ℝ × EuclideanSpace ℝ (Fin n)) → ℝ,
        U 0 = 0 ∧ AnalyticAt ℝ U 0 ∧ fderiv ℝ U 0 = 0 ∧
        (∀ᶠ z in 𝓝 0, fderiv ℝ U z (1, 0) =
          M / ((1 - ((∑ i, z.2 i) + z.1 / ρ + (m : ℝ) * U z) / R) *
            (1 - (∑ i : Fin n, ∑ _j : Fin m,
              fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R)) - M) ∧
        (∀ k (h : Fin k → ℝ × EuclideanSpace ℝ (Fin n)),
          (∀ i, 0 ≤ (h i).1 ∧ ∀ j, 0 ≤ (h i).2 j) →
          0 ≤ iteratedFDeriv ℝ k U 0 h) := by
  obtain ⟨ρ, hρ, hρle, hsmall⟩ :=
    chooseRho (n : ℝ) m M R (Nat.cast_nonneg n) (Nat.cast_nonneg m) hM hR
  have ha : 0 ≤ (n : ℝ) * m * ρ / R := by positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨v, hv0, hva, hvd0, heq, hpos⟩ :=
    collarGoursatAnalyticMajorant ((n : ℝ) * m * ρ / R) M R ρ m
      ha hM hR hρ hm' hsmall
  exact ⟨ρ, hρ, hρle, multivariateOfScalar M R ρ hρ v hv0 hva hvd0 heq hpos⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarGoursatPDEMajorant
