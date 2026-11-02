import GlobalEmbedding.Paper.CollarCKSpatialFormalSolution
import GlobalEmbedding.Paper.CollarCKAnalyticCoefficientRealization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Analytic reconstruction of the same actual formal CK coefficients

Source: Gantumur, notes2, Theorem18, coefficient convergence, pp9–10.
DAG: `collar-ck-formal-coefficient-realization`. W5 analytic realization only.
The word-index laws are the shared W6 packaging interface, not another index definition.
-/

noncomputable section
open scoped Topology ENNReal NNReal
namespace GlobalEmbedding.Paper

/-- Reconstruct exactly the coefficients of the canonical formal solution as a genuine analytic
sum. Distribute each unchanged coefficient equally over its finite coordinate-word fiber;
the denominator is at least one, and summing the fiber recovers the original coefficient.
Apply the accepted analytic coordinate-series foundation directly. Actual zero initial formal
coefficients give zero values on the entire initial hyperplane.

The geometric estimate is an intermediate input to be discharged by W4's genuine majorant.
The word laws are W6's coefficient dictionary, not extra original CK hypotheses. The actual
PDE, nonlinear analytic substitution and analytic-germ uniqueness remain parent obligations. -/
theorem collarCKFormalCoefficientRealization {n m : ℕ} (G : CollarCKRHS n m)
    (wordIndex : ∀ k : ℕ, (Fin k → CollarCKFullIndex n) → (CollarCKFullIndex n →₀ ℕ))
    (hdegree : ∀ k w, (wordIndex k w).degree = k)
    (hcover : ∀ k d, d.degree = k → ∃ w, wordIndex k w = d)
    (htime : ∀ k w, (∀ i, w i ≠ Sum.inl ()) → wordIndex k w (Sum.inl ()) = 0)
    (M s : ℝ) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hbound : ∀ (d : CollarCKFullIndex n →₀ ℕ) (j : Fin m),
      |MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)| ≤
        M * s ^ d.degree) :
    ∃ (a : ∀ k : ℕ, (Fin k → CollarCKFullIndex n) → Fin m → ℝ) (r : NNReal),
      0 < r ∧
      (HasFPowerSeriesOnBall (collarCKCoordinateSeries a).sum
        (collarCKCoordinateSeries a) 0 r ∧
        AnalyticOnNhd ℝ (collarCKCoordinateSeries a).sum (Metric.eball 0 (r : ℝ≥0∞)) ∧
        ∀ z, ‖z‖ₑ < (r : ℝ≥0∞) →
          HasFDerivAt (collarCKCoordinateSeries a).sum
            ((collarCKCoordinateSeries a).derivSeries.sum z) z) ∧
      (∀ k (d : CollarCKFullIndex n →₀ ℕ), d.degree = k → ∀ j,
        (∑ w ∈ Finset.univ.filter (fun w ↦ wordIndex k w = d),
          collarCKCoordinateSeries a k (fun i ↦ Pi.single (w i) (1 : ℝ)) j) =
          MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)) ∧
      (∀ z, z (Sum.inl ()) = 0 → (collarCKCoordinateSeries a).sum z = 0) := by
  classical
  let c (d : CollarCKFullIndex n →₀ ℕ) : Fin m → ℝ :=
    fun j ↦ MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)
  let fiber (k : ℕ) (d : CollarCKFullIndex n →₀ ℕ) :=
    Finset.univ.filter (fun w : Fin k → CollarCKFullIndex n ↦ wordIndex k w = d)
  let count (k : ℕ) (d : CollarCKFullIndex n →₀ ℕ) := (fiber k d).card
  let a (k : ℕ) (w : Fin k → CollarCKFullIndex n) : Fin m → ℝ :=
    (count k (wordIndex k w) : ℝ)⁻¹ • c (wordIndex k w)
  have hcount (k : ℕ) (w : Fin k → CollarCKFullIndex n) :
      (1 : ℝ) ≤ count k (wordIndex k w) := by
    exact_mod_cast Finset.one_le_card.mpr
      (show (fiber k (wordIndex k w)).Nonempty from ⟨w, by simp [fiber]⟩)
  have hgeom (k : ℕ) (w : Fin k → CollarCKFullIndex n) : ‖a k w‖ ≤ M * s ^ k := by
    have hc : ‖c (wordIndex k w)‖ ≤ M * s ^ k := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (pow_nonneg hs k))).mpr
      intro j
      simpa only [c, Real.norm_eq_abs, hdegree] using hbound (wordIndex k w) j
    have hcount0 : (0 : ℝ) < count k (wordIndex k w) := lt_of_lt_of_le zero_lt_one (hcount k w)
    change ‖(count k (wordIndex k w) : ℝ)⁻¹ • c (wordIndex k w)‖ ≤ M * s ^ k
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hcount0.le)]
    exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (hcount k w))
      (norm_nonneg _)).trans (by simpa only [one_mul] using hc)
  have hbasis (k : ℕ) (w : Fin k → CollarCKFullIndex n) :
      collarCKCoordinateSeries a k (fun i ↦ Pi.single (w i) (1 : ℝ)) = a k w := by
    funext j
    simp only [collarCKCoordinateSeries, sum_apply, collarCKCoordinateMonomial_apply]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      have hz : (∏ l, (Pi.single (w l) (1 : ℝ) : CollarCKFullIndex n → ℝ) (v l)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      rw [hz, zero_smul]
    · intro hw
      exact (hw (Finset.mem_univ w)).elim
  obtain ⟨r, hr, hreal⟩ := collarCKCoordinateSeries_realization_of_geometric a M s hs hgeom
  refine ⟨a, r, hr, hreal, ?_, ?_⟩
  · intro k d hd j
    obtain ⟨w, hw⟩ := hcover k d hd
    have hcard : (0 : ℝ) < count k d := by
      rw [← hw]
      exact lt_of_lt_of_le zero_lt_one (hcount k w)
    change (∑ v ∈ fiber k d,
      collarCKCoordinateSeries a k (fun i ↦ Pi.single (v i) (1 : ℝ)) j) = c d j
    calc
      _ = ∑ v ∈ fiber k d, (count k d : ℝ)⁻¹ * c d j := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvd : wordIndex k v = d := (Finset.mem_filter.mp hv).2
        rw [hbasis]
        simp only [a, hvd, Pi.smul_apply, smul_eq_mul]
      _ = (count k d : ℝ) * ((count k d : ℝ)⁻¹ * c d j) := by
        simp only [Finset.sum_const, nsmul_eq_mul, count]
      _ = c d j := by rw [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul]
  · apply collarCKCoordinateSeries_initial_hyperplane a (Sum.inl ())
    intro k w hw
    have hc0 : c (wordIndex k w) = 0 := by
      funext j
      dsimp only [c]
      rw [collarCKFlatten_coeff, htime k w hw]
      exact collarCKCoeff_initial _ (collarCKFormalSolution_spec G).1 _ _
    simp only [a, hc0, smul_zero]

/-- The same coefficient realization gives an actual jointly analytic map on the original
normal-time times Euclidean-spatial domain. The coordinate map is a genuine continuous linear
map, without identifying the Euclidean norm with a product-coordinate norm. Its entire initial
hypersurface is zero and its full Taylor fiber coefficients are those of the same formal solution.
The nonlinear PDE and analytic-germ uniqueness are still separate parent obligations. -/
theorem collarCKFormalJointAnalyticRealization {n m : ℕ} (G : CollarCKRHS n m)
    (wordIndex : ∀ k : ℕ, (Fin k → CollarCKFullIndex n) → (CollarCKFullIndex n →₀ ℕ))
    (hdegree : ∀ k w, (wordIndex k w).degree = k)
    (hcover : ∀ k d, d.degree = k → ∃ w, wordIndex k w = d)
    (htime : ∀ k w, (∀ i, w i ≠ Sum.inl ()) → wordIndex k w (Sum.inl ()) = 0)
    (M s : ℝ) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hbound : ∀ (d : CollarCKFullIndex n →₀ ℕ) (j : Fin m),
      |MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)| ≤
        M * s ^ d.degree) :
    ∃ (p : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) (Fin m → ℝ))
      (u : ℝ × EuclideanSpace ℝ (Fin n) → Fin m → ℝ) (δ : ℝ),
      0 < δ ∧ AnalyticOnNhd ℝ u (Metric.ball 0 δ) ∧
      HasFPowerSeriesAt p.sum p 0 ∧
      (∀ t x, u (t, x) = p.sum (Sum.elim (fun _ ↦ t) (fun i ↦ x i))) ∧
      (∀ x, u (0, x) = 0) ∧
      (∀ k (d : CollarCKFullIndex n →₀ ℕ), d.degree = k → ∀ j,
        (∑ w ∈ Finset.univ.filter (fun w ↦ wordIndex k w = d),
          p k (fun i ↦ Pi.single (w i) (1 : ℝ)) j) =
          MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)) := by
  obtain ⟨a, r, hr, hreal, hcoeff, hzero⟩ :=
    collarCKFormalCoefficientRealization G wordIndex hdegree hcover htime M s hM hs hbound
  let p := collarCKCoordinateSeries a
  let L : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] (CollarCKFullIndex n → ℝ) :=
    ContinuousLinearMap.pi (Sum.elim
      (fun _ ↦ ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))
      (fun i ↦ (EuclideanSpace.proj i).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n)))))
  let u : ℝ × EuclideanSpace ℝ (Fin n) → Fin m → ℝ := p.sum ∘ L
  have hp : HasFPowerSeriesAt p.sum p 0 := hreal.1.hasFPowerSeriesAt
  have ha : AnalyticAt ℝ u 0 := by
    have hpL : AnalyticAt ℝ p.sum (L 0) := by simpa only [map_zero] using hp.analyticAt
    exact hpL.comp (L.analyticAt 0)
  obtain ⟨δ, hδ, hu⟩ := ha.exists_ball_analyticOnNhd
  refine ⟨p, u, δ, hδ, hu, hp, ?_, ?_, hcoeff⟩
  · intro t x
    change p.sum (L (t, x)) = _
    congr 1
    funext v
    rcases v with ⟨⟩ | i
    · rfl
    · simp [L]
  · intro x
    exact hzero (L (0, x)) rfl

#print axioms collarCKFormalCoefficientRealization
#print axioms collarCKFormalJointAnalyticRealization
end GlobalEmbedding.Paper
