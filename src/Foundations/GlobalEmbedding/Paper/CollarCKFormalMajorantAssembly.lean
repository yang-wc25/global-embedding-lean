import GlobalEmbedding.Paper.CollarCKRationalCoefficientMajorant
import GlobalEmbedding.Paper.CollarCKLocalMajorantComparison
import GlobalEmbedding.Paper.CollarCKAnalyticTaylorPackaging
import GlobalEmbedding.Paper.CollarCKFlattenSubstitution
import GlobalEmbedding.Paper.CollarCKGoursatFormalRHS

/-!
# Reusable majorant assembly adapters for the actual CK data

Source: Gantumur, Math580 notes2, Theorem18, pp9–10.
DAG: `collar-ck-formal-majorant-assembly`. Exclusive owner W4.
These three existing proofs are extracted from the compiled original parent checkpoint.
They discharge actual RHS bounds and unknown-side formal identities. The scalar actual
Goursat Taylor PDE bridge is still required by the complete original domination theorem.
-/

noncomputable section
open scoped BigOperators

namespace GlobalEmbedding.Paper

/-- Specialize the accepted double induction to the SAME actual canonical formal solution.
All unknown-side slot, substitution, PDE, and initial identities are discharged here by the
accepted W3 provider. The remaining scalar-majorant data are the W6 bridge interface,
and RHS domination is to be supplied by the actual analytic geometric estimate. -/
theorem collarCKFormalSolution_dominated {n m : ℕ} (G : CollarCKRHS n m)
    (U : MvPowerSeries (CollarCKFullIndex n) ℝ)
    (F : MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ)
    (A : Fin n ⊕ CollarCKSlot n m → MvPowerSeries (CollarCKFullIndex n) ℝ)
    (hH : ∀ j, CollarCKCoeffDominated (collarCKFullRHS G j) F)
    (hA : MvPowerSeries.HasSubst A)
    (hAx : ∀ i, A (Sum.inl i) = MvPowerSeries.X (Sum.inr i))
    (hAt : A (Sum.inr (Sum.inl ())) = MvPowerSeries.X (Sum.inl ()))
    (hAy : ∀ j, A (Sum.inr (Sum.inr (Sum.inl j))) = U)
    (hAp : ∀ i j, A (Sum.inr (Sum.inr (Sum.inr (i, j)))) =
      MvPowerSeries.pderiv (Sum.inr i) U)
    (hU : MvPowerSeries.pderiv (Sum.inl ()) U = MvPowerSeries.subst A F)
    (hpos : ∀ d, 0 ≤ MvPowerSeries.coeff d U) :
    ∀ j, CollarCKCoeffDominated (collarCKFlatten (collarCKFormalSolution G) j) U := by
  classical
  let u := collarCKFormalSolution G
  have hu0 : PowerSeries.constantCoeff u = 0 := (collarCKFormalSolution_spec G).1
  have hX (i : CollarCKFullIndex n) :
      CollarCKCoeffDominated (MvPowerSeries.X i : MvPowerSeries _ ℝ)
        (MvPowerSeries.X i) := by
    intro d
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> norm_num
  apply collarCK_formal_coefficient_comparison (collarCKFlatten u) U
    (collarCKFullRHS G) F hH (collarCKFullSlots u) A
    (collarCKFullSlots_hasSubst u hu0) hA
  · intro s
    rcases s with i | (⟨⟩ | (j | ⟨i, j⟩))
    · left
      rw [collarCKFullSlots_spatial, hAx]
      exact hX _
    · left
      rw [collarCKFullSlots_time, hAt]
      exact hX _
    · right; left
      exact ⟨j, collarCKFullSlots_value u j, hAy j⟩
    · right; right
      exact ⟨i, j, collarCKFullSlots_gradient u i j, hAp i j⟩
  · exact collarCKFormalSolution_fullEquation G
  · exact hU
  · intro j d hd
    rw [collarCKFlatten_coeff, hd]
    simp [collarCKCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, hu0]
  · exact hpos

/-- Domination by the SAME genuinely convergent scalar Taylor series gives the geometric
bound needed by the accepted analytic realization. This applies the existing finite-word
estimate to the shared literal fiber, without any further coefficient extraction. -/
theorem collarCKFormalSolution_geometric_of_domination {n m : ℕ} (G : CollarCKRHS n m)
    (p : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ)
    (hp : 0 < p.radius)
    (hdom : ∀ j, CollarCKCoeffDominated (collarCKFlatten (collarCKFormalSolution G) j)
      (fun d ↦ collarCKTaylorCoeff p d)) :
    ∃ M s : ℝ, 0 < M ∧ 0 < s ∧ ∀ (d : CollarCKFullIndex n →₀ ℕ) (j : Fin m),
      |MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)| ≤
        M * s ^ d.degree := by
  classical
  have he (i : CollarCKFullIndex n) :
      ‖(Pi.single i (1 : ℝ) : CollarCKFullIndex n → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    by_cases hj : j = i <;> simp [hj]
  obtain ⟨M, R, hM, hR, hb⟩ :=
    collarCKFiniteCoordinateGeometricBound p hp (fun i ↦ Pi.single i (1 : ℝ)) he
  refine ⟨M, R⁻¹, hM, inv_pos.mpr hR, ?_⟩
  intro d j
  have hcoef : |collarCKTaylorCoeff p d| ≤ M / R ^ d.degree := by
    simpa only [collarCKTaylorCoeff, Real.norm_eq_abs] using
      hb d.degree (collarCKWordFiber d)
  calc
    |MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j)| ≤
        collarCKTaylorCoeff p d := hdom j d
    _ ≤ |collarCKTaylorCoeff p d| := le_abs_self _
    _ ≤ M / R ^ d.degree := hcoef
    _ = M * (R⁻¹) ^ d.degree := by rw [div_eq_mul_inv, inv_pow]

/-- Original analytic CK data construct the SAME normalized Taylor RHS and actual positive
majorant constants. Every allowed Goursat time weight then gives genuine RHS domination.
Source: Gantumur, Theorem18. Reuse the actual original-data Taylor packaging; its literal
full coefficients give the geometric estimate and its origin coefficient is zero.
The scalar Goursat PDE bridge and unknown-solution comparison are subsequent steps. -/
theorem collarCKOriginalData_rhs_majorant {n m : ℕ}
    (G : EuclideanSpace ℝ (Fin n) × ℝ × (Fin m → ℝ) × (Fin n → Fin m → ℝ) →
      Fin m → ℝ)
    (v₀ : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)) :
    ∃ p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ),
      HasFPowerSeriesAt
        (collarCKNormalizedRHS G v₀ x₀ ∘ collarCKRHSCoordinates) p 0 ∧
      (∀ v, p 0 v = 0) ∧
      ∃ M R : ℝ, 0 < M ∧ 0 < R ∧ ∀ rho : ℝ, 0 < rho → rho ≤ 1 → ∀ j,
        CollarCKCoeffDominated (collarCKFullRHS (collarCKTaylorRHS p) j)
          (collarCKGoursatRHS n m M R rho) := by
  classical
  obtain ⟨p, hp, _, hp0, M, R, hM, hR, hb⟩ :=
    collarCKOriginalData_taylor G v₀ x₀ hv₀ hG
  refine ⟨p, hp, hp0, M, R, hM, hR, ?_⟩
  intro rho hrho hrho1 j
  apply collarCK_goursat_rhs_domination _ M R rho hM.le hR hrho hrho1
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change MvPowerSeries.coeff
      (Finsupp.comapDomain Sum.inl 0 Sum.inl_injective.injOn)
      (MvPowerSeries.coeff (Finsupp.comapDomain Sum.inr 0 Sum.inr_injective.injOn)
        (collarCKTaylorRHS p j)) = 0
    simpa using collarCKTaylorRHS_origin p hp0 j
  · intro d
    change |MvPowerSeries.coeff
      (Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn)
      (MvPowerSeries.coeff (Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn)
        (collarCKTaylorRHS p j))| ≤ _
    simpa only [Finsupp.comapDomain_sumElim_comapDomain] using
      hb j (Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn)
        (Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKFormalSolution_dominated
#print axioms GlobalEmbedding.Paper.collarCKFormalSolution_geometric_of_domination
#print axioms GlobalEmbedding.Paper.collarCKOriginalData_rhs_majorant
