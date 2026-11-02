import GlobalEmbedding.Paper.CollarCKAnalyticTaylorPackaging
import GlobalEmbedding.Paper.CollarGoursatPDEMajorant
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Positivity of the actual Goursat Taylor coefficients

Source: Gantumur, notes2, Theorem 18, equations 47–51.
Use the shared word multiplicity and coefficient definitions. An individual nonsymmetric
multilinear coefficient need not be positive. Summing the actual derivative permutation formula
over a complete word fiber proves positivity of the genuine commutative coefficient.
-/

noncomputable section
open scoped BigOperators Topology
namespace GlobalEmbedding.Paper

variable {σ : Type*}

/-- Permuting word positions preserves their actual multiplicities.
Source: Gantumur, commutative Taylor expansion; reindex the native finite singleton sum. -/
theorem collarCKWordIndex_comp_perm {k : ℕ} (w : Fin k → σ) (τ : Equiv.Perm (Fin k)) :
    collarCKWordIndex (w ∘ τ) = collarCKWordIndex w := by
  classical
  exact Equiv.sum_comp τ (fun i ↦ Finsupp.single (w i) 1)

/-- A permutation of positions bijects each complete shared word fiber, preserving its sum.
Source: Gantumur, Taylor coefficient grouping. The inverse bijection composes with `τ.symm`. -/
theorem collarCKWordFiber_sum_perm [Fintype σ] [DecidableEq σ]
    (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (d : σ →₀ ℕ)
    (τ : Equiv.Perm (Fin d.degree)) :
    (∑ w ∈ collarCKWordFiber d, p d.degree (fun i ↦ Pi.single (w (τ i)) 1)) =
      collarCKTaylorCoeff p d := by
  classical
  unfold collarCKTaylorCoeff
  refine Finset.sum_bij (fun w _ ↦ w ∘ τ) ?_ ?_ ?_ ?_
  · intro w hw
    simpa only [collarCKWordFiber, Finset.mem_filter, Finset.mem_univ, true_and,
      collarCKWordIndex_comp_perm] using hw
  · intro w hw v hv heq
    funext i
    simpa only [Function.comp_apply, τ.apply_symm_apply] using congrFun heq (τ.symm i)
  · intro w hw
    refine ⟨w ∘ τ.symm, ?_, ?_⟩
    · simpa only [collarCKWordFiber, Finset.mem_filter, Finset.mem_univ, true_and,
        collarCKWordIndex_comp_perm] using hw
    · funext i
      exact congrArg w (τ.symm_apply_apply i)
  · intro w _
    rfl

/-- The shared coefficient is intrinsically determined by the actual coordinate derivatives.
Source: Gantumur, Taylor coefficient grouping. Apply the native derivative permutation formula
and sum over the complete shared word fiber. Interchange the two finite sums; every permutation
bijects the same fiber, so there are exactly `degree!` equal copies of its coefficient. -/
theorem collarCKTaylorCoeff_factorial [Fintype σ] [DecidableEq σ]
    (f : (σ → ℝ) → ℝ) (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0) (d : σ →₀ ℕ) :
    (d.degree.factorial : ℝ) * collarCKTaylorCoeff p d =
      ∑ w ∈ collarCKWordFiber d,
        iteratedFDeriv ℝ d.degree f 0 (fun i ↦ Pi.single (w i) 1) := by
  classical
  obtain ⟨r, hr⟩ := hp
  simp_rw [hr.iteratedFDeriv_eq_sum_of_completeSpace]
  rw [Finset.sum_comm]
  simp only [collarCKWordFiber_sum_perm, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- Actual nonnegative coordinate derivatives force nonnegative shared commutative coefficients.
Source: Gantumur, positivity of the majorant Taylor series. The preceding identity expresses
the positive factorial times the coefficient as a sum of nonnegative actual derivatives. -/
theorem collarCKTaylorCoeff_nonneg_of_derivatives [Fintype σ] [DecidableEq σ]
    (f : (σ → ℝ) → ℝ) (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hpos : ∀ k (w : Fin k → σ),
      0 ≤ iteratedFDeriv ℝ k f 0 (fun i ↦ Pi.single (w i) 1)) (d : σ →₀ ℕ) :
    0 ≤ collarCKTaylorCoeff p d := by
  classical
  have hsum : 0 ≤ ∑ w ∈ collarCKWordFiber d,
      iteratedFDeriv ℝ d.degree f 0 (fun i ↦ Pi.single (w i) 1) := by
    apply Finset.sum_nonneg
    intro w _
    exact hpos d.degree w
  rw [← collarCKTaylorCoeff_factorial f p hp d] at hsum
  exact nonneg_of_mul_nonneg_right hsum (by positivity : (0 : ℝ) < (d.degree.factorial : ℝ))

/-- The canonical full time/spatial coordinates identify the original native domain continuously.
Source: Gantumur, Theorem 18. This uses the existing full index, and asserts no equality of norms.
W5's inverse realization uses the inverse of this same literal coordinate formula. -/
def collarCKFullCoordinates {n : ℕ} :
    (CollarCKFullIndex n → ℝ) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z ↦ (z (Sum.inl ()), WithLp.toLp 2 (fun i ↦ z (Sum.inr i)))
      invFun := fun z ↦ Sum.elim (fun _ ↦ z.1) (fun i ↦ z.2 i)
      left_inv := by intro z; funext i; rcases i with ⟨⟩ | i <;> rfl
      right_inv := by intro z; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Coordinate basis directions map to coordinatewise nonnegative original directions.
Source: Gantumur, positivity of the symmetric majorant derivatives. Inspect each time/spatial
coordinate of the literal basis vector; every coordinate is zero or one. -/
theorem collarCKFullCoordinates_basis_nonneg {n : ℕ} (a : CollarCKFullIndex n) :
    0 ≤ (collarCKFullCoordinates (Pi.single a 1)).1 ∧
      ∀ j, 0 ≤ (collarCKFullCoordinates (Pi.single a 1)).2 j := by
  classical
  constructor
  · change 0 ≤ (Pi.single a (1 : ℝ) : CollarCKFullIndex n → ℝ) (Sum.inl ())
    by_cases h : Sum.inl () = a <;> simp [h]
  · intro j
    change 0 ≤ (Pi.single a (1 : ℝ) : CollarCKFullIndex n → ℝ) (Sum.inr j)
    by_cases h : Sum.inr j = a <;> simp [h]

/-- The same actual analytic scalar majorant has genuine nonnegative full Taylor coefficients,
with zero origin and first jet in the shared coefficient convention.
Source: Gantumur, Theorem 18. Pull the actual expansion back by the canonical continuous linear
coordinates. The native iterated-derivative identity for a linear equivalence transfers actual
nonnegativity on basis directions; the permutation/fiber argument above then gives coefficient
nonnegativity. The zeroth and first actual derivative determine the corresponding coefficients. -/
theorem collarCKAnalyticMajorant_taylor_positive {n : ℕ}
    (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (hU : AnalyticAt ℝ U 0) (hU0 : U 0 = 0) (hD0 : fderiv ℝ U 0 = 0)
    (hpos : ∀ k (h : Fin k → ℝ × EuclideanSpace ℝ (Fin n)),
      (∀ i, 0 ≤ (h i).1 ∧ ∀ j, 0 ≤ (h i).2 j) →
      0 ≤ iteratedFDeriv ℝ k U 0 h) :
    ∃ p : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ,
      HasFPowerSeriesAt (U ∘ collarCKFullCoordinates) p 0 ∧
      (∀ d, 0 ≤ collarCKTaylorCoeff p d) ∧ collarCKTaylorCoeff p 0 = 0 ∧
      (∀ d, d.degree = 1 → collarCKTaylorCoeff p d = 0) := by
  classical
  let L := collarCKFullCoordinates (n := n)
  have ha : AnalyticAt ℝ (U ∘ L) 0 :=
    hU.comp_of_eq (L.toContinuousLinearMap.analyticAt 0) (map_zero _)
  obtain ⟨p, hp⟩ := ha
  have hpositive (k : ℕ) (w : Fin k → CollarCKFullIndex n) :
      0 ≤ iteratedFDeriv ℝ k (U ∘ L) 0 (fun i ↦ Pi.single (w i) 1) := by
    have hcomp := L.iteratedFDerivWithin_comp_right U uniqueDiffOn_univ
      (Set.mem_univ (L 0)) k
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] at hcomp
    rw [hcomp]
    apply hpos
    intro i
    exact collarCKFullCoordinates_basis_nonneg (w i)
  have hd : fderiv ℝ (U ∘ L) 0 = 0 := by
    have hUL : DifferentiableAt ℝ U (L 0) := by
      simpa only [map_zero] using hU.differentiableAt
    simpa only [map_zero, hD0, ContinuousLinearMap.zero_comp] using
      (hUL.hasFDerivAt.comp 0 L.hasFDerivAt).fderiv
  have hp1 : p 1 = 0 := by
    apply (continuousMultilinearCurryFin1 ℝ (CollarCKFullIndex n → ℝ) ℝ).injective
    simpa only [map_zero] using hp.fderiv_eq.symm.trans hd
  refine ⟨p, hp, collarCKTaylorCoeff_nonneg_of_derivatives (U ∘ L) p hp hpositive, ?_, ?_⟩
  · apply collarCKTaylorCoeff_zero
    intro v
    simpa only [Function.comp_apply, map_zero] using (hp.coeff_zero v).trans hU0
  · intro d hd
    unfold collarCKTaylorCoeff
    apply Finset.sum_eq_zero
    intro w _
    have hterm : p d.degree = 0 := by rw [hd, hp1]
    rw [hterm]
    rfl

/-- The accepted actual Goursat construction supplies the same analytic majorant and genuine
nonnegative shared Taylor coefficients, including its zero origin and first jet.
Source: Gantumur, Theorem 18, equations 47–51.
Call the accepted majorant exactly once and apply the preceding actual coefficient theorem to
that very function. Keep its original near-origin rational PDE unchanged for the separate
formal Taylor-calculus bridge. No desired coefficient sign or formal PDE is an input here. -/
theorem collarCKGoursat_taylor_positive (n m : ℕ) (hm : 0 < m)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∃ (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
        (p : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ),
        U 0 = 0 ∧ AnalyticAt ℝ U 0 ∧ fderiv ℝ U 0 = 0 ∧
        (∀ᶠ z in 𝓝 0, fderiv ℝ U z (1, 0) =
          M / ((1 - ((∑ i, z.2 i) + z.1 / ρ + (m : ℝ) * U z) / R) *
            (1 - (∑ i : Fin n, ∑ _j : Fin m,
              fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R)) - M) ∧
        HasFPowerSeriesAt (U ∘ collarCKFullCoordinates) p 0 ∧
        (∀ d, 0 ≤ collarCKTaylorCoeff p d) ∧ collarCKTaylorCoeff p 0 = 0 ∧
        (∀ d, d.degree = 1 → collarCKTaylorCoeff p d = 0) := by
  obtain ⟨ρ, hρ, hρle, U, hU0, hUa, hD0, heq, hpos⟩ :=
    collarGoursatPDEMajorant n m hm M R hM hR
  obtain ⟨p, hp, hcoeff, hp0, hp1⟩ :=
    collarCKAnalyticMajorant_taylor_positive U hUa hU0 hD0 hpos
  exact ⟨ρ, hρ, hρle, U, p, hU0, hUa, hD0, heq, hp, hcoeff, hp0, hp1⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKWordIndex_comp_perm
#print axioms GlobalEmbedding.Paper.collarCKWordFiber_sum_perm
#print axioms GlobalEmbedding.Paper.collarCKTaylorCoeff_factorial
#print axioms GlobalEmbedding.Paper.collarCKTaylorCoeff_nonneg_of_derivatives
#print axioms GlobalEmbedding.Paper.collarCKFullCoordinates
#print axioms GlobalEmbedding.Paper.collarCKFullCoordinates_basis_nonneg
#print axioms GlobalEmbedding.Paper.collarCKAnalyticMajorant_taylor_positive
#print axioms GlobalEmbedding.Paper.collarCKGoursat_taylor_positive
