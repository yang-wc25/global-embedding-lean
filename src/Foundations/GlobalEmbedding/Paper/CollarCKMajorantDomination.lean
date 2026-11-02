import GlobalEmbedding.Paper.CollarCKFormalMajorantAssembly
import GlobalEmbedding.Paper.CollarCKGoursatTaylorBridge

/-!
# Actual analytic CK majorant domination

Source: Gantumur, Math580 notes2, Theorem18, pp9–10.
DAG: `collar-ck-majorant-domination`. Exclusive owner W4.
The same original analytic data construct the actual normalized RHS, one genuine analytic
Goursat majorant, and coefficient domination of the actual canonical formal solution.
All scalar Taylor calculus and formal-PDE identities are consumed from their sole providers.
-/

noncomputable section
open scoped BigOperators Topology

namespace GlobalEmbedding.Paper

/-- Original analytic CK data construct one actual scalar Goursat majorant dominating every
coefficient of every component of the SAME canonical formal solution.

Source: Gantumur, Math580 notes2, Theorem18, pp9–10. The accepted original-data adapter chooses
the genuine normalized RHS expansion and positive M/R. The accepted Goursat constructor is
called once, retaining its actual native rational PDE and the same nonnegative Taylor witness.
The accepted analytic factor witnesses and cleared-coordinate equation feed the sole formal
Taylor PDE bridge. The existing native rational equivalence gives lawful same-U substitution.
The accepted double-induction adapter discharges the actual unknown's slots, PDE and initial
coefficients, without an assumed solution bound. Finally, the same convergent majorant Taylor
series gives the actual solution's geometric coefficient bound. Pure-spatial initial majorant
coefficients may be nonzero. No scalar PDE, desired domination or geometric bound is an input. -/
theorem collarCKOriginalData_majorant_domination {n m : ℕ} (hm : 0 < m)
    (G : EuclideanSpace ℝ (Fin n) × ℝ × (Fin m → ℝ) × (Fin n → Fin m → ℝ) →
      Fin m → ℝ)
    (v₀ : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)) :
    ∃ p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ),
      HasFPowerSeriesAt
        (collarCKNormalizedRHS G v₀ x₀ ∘ collarCKRHSCoordinates) p 0 ∧
      (∀ v, p 0 v = 0) ∧
      ∃ (M R rho : ℝ) (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
        (q : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ),
        0 < M ∧ 0 < R ∧ 0 < rho ∧ rho ≤ 1 ∧ U 0 = 0 ∧ AnalyticAt ℝ U 0 ∧
        fderiv ℝ U 0 = 0 ∧
        (∀ᶠ z in 𝓝 0, fderiv ℝ U z (1, 0) =
          M / ((1 - ((∑ i, z.2 i) + z.1 / rho + (m : ℝ) * U z) / R) *
            (1 - (∑ i : Fin n, ∑ _j : Fin m,
              fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R)) - M) ∧
        HasFPowerSeriesAt (U ∘ collarCKFullCoordinates) q 0 ∧
        (∀ d, 0 ≤ collarCKTaylorCoeff q d) ∧ collarCKTaylorCoeff q 0 = 0 ∧
        (∀ i, collarCKTaylorCoeff q (Finsupp.single i 1) = 0) ∧
        (MvPowerSeries.pderiv (Sum.inl ())
          (fun d ↦ collarCKTaylorCoeff q d : MvPowerSeries (CollarCKFullIndex n) ℝ) =
          MvPowerSeries.subst (collarCKGoursatSlots (m := m)
            (fun d ↦ collarCKTaylorCoeff q d)) (collarCKGoursatRHS n m M R rho)) ∧
        (∀ j, CollarCKCoeffDominated
          (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)
          (fun d ↦ collarCKTaylorCoeff q d)) ∧
        ∃ K s : ℝ, 0 < K ∧ 0 < s ∧ ∀ (d : CollarCKFullIndex n →₀ ℕ) (j : Fin m),
          |MvPowerSeries.coeff d
            (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)| ≤
              K * s ^ d.degree := by
  obtain ⟨p, hp, hp0, M, R, hM, hR, hH⟩ :=
    collarCKOriginalData_rhs_majorant G v₀ x₀ hv₀ hG
  obtain ⟨rho, hrho, hrho1, U, q, hU0, hU, hD0, heq, hq, hpos, hq0, hq1⟩ :=
    collarCKGoursat_taylor_positive n m hm M R hM.le hR
  obtain ⟨qt, qa, qb, hqt, hqa, hqb⟩ := collarCKGoursat_factor_expansions m R rho U hU
  have hsingle (i : CollarCKFullIndex n) :
      collarCKTaylorCoeff q (Finsupp.single i 1) = 0 :=
    hq1 _ (Finsupp.degree_single _ _)
  have hformal := collarCKGoursat_cleared_formalPDE M R rho U q qt qa qb hq hqt hqa hqb
    (collarCKGoursat_cleared_coordinatePDE M R rho U hU hU0 hD0 heq)
  have hPDE := (collarCKGoursatRHS_equation_iff (m := m) M R rho
    (fun d ↦ collarCKTaylorCoeff q d) hq0 hsingle).mpr hformal
  have hdom := collarCKFormalSolution_dominated (collarCKTaylorRHS p)
    (fun d ↦ collarCKTaylorCoeff q d) (collarCKGoursatRHS n m M R rho)
    (collarCKGoursatSlots (m := m) (fun d ↦ collarCKTaylorCoeff q d))
    (hH rho hrho hrho1) (collarCKGoursatSlots_hasSubst _ hq0 hsingle)
    (fun _ ↦ rfl) rfl (fun _ ↦ rfl) (fun _ _ ↦ rfl) hPDE hpos
  exact ⟨p, hp, hp0, M, R, rho, U, q, hM, hR, hrho, hrho1, hU0, hU, hD0, heq,
    hq, hpos, hq0, hsingle, hPDE, hdom,
    collarCKFormalSolution_geometric_of_domination (collarCKTaylorRHS p) q hq.radius_pos hdom⟩

/-- Direct geometric-bound interface for the analytic realization, with only original CK data.
Source: Gantumur, Theorem18, convergence step. Retain the SAME genuine normalized RHS witness
and the actual canonical formal solution from the complete majorant construction above.
For zero components the bound is vacuous; positivity of m is confined to the majorant branch.
Zero spatial dimension is allowed throughout. -/
theorem collarCKOriginalData_formal_geometric {n m : ℕ}
    (G : EuclideanSpace ℝ (Fin n) × ℝ × (Fin m → ℝ) × (Fin n → Fin m → ℝ) →
      Fin m → ℝ)
    (v₀ : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)) :
    ∃ p : FormalMultilinearSeries ℝ ((Fin n ⊕ CollarCKSlot n m) → ℝ) (Fin m → ℝ),
      HasFPowerSeriesAt
        (collarCKNormalizedRHS G v₀ x₀ ∘ collarCKRHSCoordinates) p 0 ∧
      (∀ v, p 0 v = 0) ∧
      ∃ K s : ℝ, 0 < K ∧ 0 < s ∧ ∀ (d : CollarCKFullIndex n →₀ ℕ) (j : Fin m),
        |MvPowerSeries.coeff d
          (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)| ≤
            K * s ^ d.degree := by
  by_cases hm : 0 < m
  · obtain ⟨p, hp, hp0, M, R, rho, U, q, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgeom⟩ :=
      collarCKOriginalData_majorant_domination hm G v₀ x₀ hv₀ hG
    exact ⟨p, hp, hp0, hgeom⟩
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    obtain ⟨p, hp, _, hp0, _⟩ := collarCKOriginalData_taylor G v₀ x₀ hv₀ hG
    refine ⟨p, hp, hp0, 1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro d j
    exact Fin.elim0 j

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKOriginalData_majorant_domination
#print axioms GlobalEmbedding.Paper.collarCKOriginalData_formal_geometric
