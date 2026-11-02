import GlobalEmbedding.Paper.CollarCKGoursatAnalyticPrepared
import GlobalEmbedding.Paper.CollarCKAnalyticTaylorCalculus
import GlobalEmbedding.Paper.CollarCKTaylorScalarCoordinate

/-!
# The same actual Goursat majorant satisfies the full formal Taylor PDE

Source: Gantumur, notes2, Theorem 18, equations 47–51.
All actual data and coefficients are the same ones in the accepted prepared provider.
The accepted scalar calculus transports the actual cleared PDE; native formal algebra
then restores the exact rational substitution equation, without a formal PDE hypothesis.
-/

noncomputable section
open scoped BigOperators Topology
namespace GlobalEmbedding.Paper

/-- Transport the actual cleared coordinate PDE of the same analytic scalar function to the
native formal ring. Source: Gantumur, Theorem 18. Use only the accepted derivative, coordinate,
linear and product Taylor laws. Construct the finite sums of genuine expansions, identify
both actual denominator witnesses by accepted witness independence, and take the package of
the actual polynomial identity as a germ equality. No formal PDE identity is an input. -/
theorem collarCKGoursat_cleared_formalPDE {n m : ℕ} (M R rho : ℝ)
    (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (p qt qa qb : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ)
    (hp : HasFPowerSeriesAt (U ∘ collarCKFullCoordinates) p 0)
    (hqt : HasFPowerSeriesAt
      (fun z ↦ fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inl ()) 1)) qt 0)
    (hqa : HasFPowerSeriesAt (fun z ↦ 1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) +
      rho⁻¹ * z (Sum.inl ()) + (∑ _j : Fin m, U (collarCKFullCoordinates z)))) qa 0)
    (hqb : HasFPowerSeriesAt (fun z ↦ 1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
      fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1))) qb 0)
    (heq : ∀ᶠ z : CollarCKFullIndex n → ℝ in 𝓝 0,
      (fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inl ()) 1) + M) *
        (1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) + rho⁻¹ * z (Sum.inl ()) +
          (∑ _j : Fin m, U (collarCKFullCoordinates z)))) *
        (1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
          fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1))) = M) :
    let u : MvPowerSeries (CollarCKFullIndex n) ℝ := fun d ↦ collarCKTaylorCoeff p d
    (MvPowerSeries.pderiv (Sum.inl ()) u + MvPowerSeries.C M) *
      (1 - R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inr i)) +
        rho⁻¹ • MvPowerSeries.X (Sum.inl ()) + (∑ _j : Fin m, u))) *
      (1 - R⁻¹ • (∑ i : Fin n, ∑ _j : Fin m,
        MvPowerSeries.pderiv (Sum.inr i) u)) = MvPowerSeries.C M := by
  classical
  intro u
  let f := U ∘ collarCKFullCoordinates
  let T : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ →ₗ[ℝ]
      MvPowerSeries (CollarCKFullIndex n) ℝ :=
    { toFun := fun q d ↦ collarCKTaylorCoeff q d
      map_add' := collarCKTaylorPackage_add
      map_smul' := by
        intro a q
        apply MvPowerSeries.ext
        intro d
        exact collarCKTaylorCoeff_smul a q d }
  have hsame (g : (CollarCKFullIndex n → ℝ) → ℝ) (q r)
      (hq : HasFPowerSeriesAt g q 0) (hr : HasFPowerSeriesAt g r 0) : T q = T r := by
    apply MvPowerSeries.ext
    intro d
    exact collarCKTaylorCoeff_unique g q r hq hr d
  let c (a : ℝ) := constFormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) a
  have hc (a : ℝ) : T (c a) = MvPowerSeries.C a := collarCKTaylorPackage_const a
  have hsum {α : Type} (s : Finset α)
      (g : α → (CollarCKFullIndex n → ℝ) → ℝ)
      (q : α → FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ)
      (hq : ∀ i ∈ s, HasFPowerSeriesAt (g i) (q i) 0) :
      HasFPowerSeriesAt (fun z ↦ ∑ i ∈ s, g i z) (∑ i ∈ s, q i) 0 := by
    induction s using Finset.induction with
    | empty => simpa using (hasFPowerSeriesAt_const (c := (0 : ℝ)))
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hq i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj ↦ hq j (Finset.mem_insert_of_mem hj)))
  let qx (i : CollarCKFullIndex n) :=
    (ContinuousLinearMap.proj i : (CollarCKFullIndex n → ℝ) →L[ℝ] ℝ).fpowerSeries 0
  have hqx (i) : HasFPowerSeriesAt (fun z : CollarCKFullIndex n → ℝ ↦ z i) (qx i) 0 :=
    (ContinuousLinearMap.proj i : (CollarCKFullIndex n → ℝ) →L[ℝ] ℝ).hasFPowerSeriesAt 0
  have hTx (i) : T (qx i) = MvPowerSeries.X i :=
    collarCKTaylorPackage_scalar_coordinate i (qx i) (hqx i)
  have hpartial (i : Fin n) : AnalyticAt ℝ
      (fun z ↦ fderiv ℝ f z (Pi.single (Sum.inr i) 1)) 0 :=
    ((ContinuousLinearMap.apply ℝ ℝ
      (Pi.single (Sum.inr i) 1 : CollarCKFullIndex n → ℝ)).analyticAt _).comp hp.analyticAt.fderiv
  choose qd hqd using hpartial
  have hTd (i : Fin n) : T (qd i) = MvPowerSeries.pderiv (Sum.inr i) u :=
    collarCKTaylorPackage_partial f p (qd i) hp (Sum.inr i) (hqd i)
  have hTt : T qt = MvPowerSeries.pderiv (Sum.inl ()) u :=
    collarCKTaylorPackage_partial f p qt hp (Sum.inl ()) hqt
  let a := c 1 - R⁻¹ • ((∑ i : Fin n, qx (Sum.inr i)) +
    rho⁻¹ • qx (Sum.inl ()) + (∑ _j : Fin m, p))
  let b := c 1 - R⁻¹ • (∑ i : Fin n, ∑ _j : Fin m, qd i)
  have hsx : HasFPowerSeriesAt
      (fun z : CollarCKFullIndex n → ℝ ↦ ∑ i : Fin n, z (Sum.inr i))
      (∑ i : Fin n, qx (Sum.inr i)) 0 :=
    hsum (Finset.univ : Finset (Fin n))
      (fun i : Fin n ↦ fun z : CollarCKFullIndex n → ℝ ↦ z (Sum.inr i))
      (fun i : Fin n ↦ qx (Sum.inr i)) (fun i _ ↦ hqx (Sum.inr i))
  have hsv : HasFPowerSeriesAt
      (fun z : CollarCKFullIndex n → ℝ ↦ ∑ _j : Fin m, f z) (∑ _j : Fin m, p) 0 :=
    hsum (Finset.univ : Finset (Fin m)) (fun _ : Fin m ↦ f)
      (fun _ : Fin m ↦ p) (fun _ _ ↦ hp)
  have hst := (hqx (Sum.inl ())).const_smul (c := rho⁻¹)
  have ha : HasFPowerSeriesAt
      (fun z ↦ 1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) +
        rho⁻¹ * z (Sum.inl ()) + (∑ _j : Fin m, f z))) a 0 := by
    exact (hasFPowerSeriesAt_const (c := (1 : ℝ))).sub
      (((hsx.add hst).add hsv).const_smul (c := R⁻¹))
  have hsd (i : Fin n) : HasFPowerSeriesAt
      (fun z ↦ ∑ _j : Fin m, fderiv ℝ f z (Pi.single (Sum.inr i) 1))
      (∑ _j : Fin m, qd i) 0 :=
    hsum (Finset.univ : Finset (Fin m))
      (fun _ : Fin m ↦ fun z : CollarCKFullIndex n → ℝ ↦
        fderiv ℝ f z (Pi.single (Sum.inr i) 1))
      (fun _ : Fin m ↦ qd i) (fun _ _ ↦ hqd i)
  have hsdall : HasFPowerSeriesAt
      (fun z ↦ ∑ i : Fin n, ∑ _j : Fin m,
        fderiv ℝ f z (Pi.single (Sum.inr i) 1))
      (∑ i : Fin n, ∑ _j : Fin m, qd i) 0 :=
    hsum (Finset.univ : Finset (Fin n))
      (fun i : Fin n ↦ fun z : CollarCKFullIndex n → ℝ ↦
        ∑ _j : Fin m, fderiv ℝ f z (Pi.single (Sum.inr i) 1))
      (fun i : Fin n ↦ ∑ _j : Fin m, qd i) (fun i _ ↦ hsd i)
  have hb : HasFPowerSeriesAt (fun z ↦ 1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
      fderiv ℝ f z (Pi.single (Sum.inr i) 1))) b 0 :=
    (hasFPowerSeriesAt_const (c := (1 : ℝ))).sub (hsdall.const_smul (c := R⁻¹))
  have hTa : T qa = 1 - R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inr i)) +
      rho⁻¹ • MvPowerSeries.X (Sum.inl ()) + (∑ _j : Fin m, u)) := by
    rw [hsame _ qa a hqa ha]
    simp only [a, map_sub, map_smul, map_add, map_sum, hc, hTx, map_one]
    rfl
  have hTb : T qb = 1 - R⁻¹ • (∑ i : Fin n, ∑ _j : Fin m,
      MvPowerSeries.pderiv (Sum.inr i) u) := by
    rw [hsame _ qb b hqb hb]
    simp only [b, map_sub, map_smul, map_sum, hc, hTd, map_one]
  have hplus : T (qt + c M) = MvPowerSeries.pderiv (Sum.inl ()) u + MvPowerSeries.C M := by
    rw [map_add, hTt, hc]
  have hmul1 := (hqt.add (hasFPowerSeriesAt_const (c := M))).analyticAt.mul hqa.analyticAt
  obtain ⟨r, hr⟩ := hmul1
  have hmul2 := hr.analyticAt.mul hqb.analyticAt
  obtain ⟨s, hs⟩ := hmul2
  have hR : T r = T (qt + c M) * T qa :=
    collarCKTaylorPackage_mul _ _ (qt + c M) qa r
      (hqt.add hasFPowerSeriesAt_const) hqa hr
  have hS : T s = T r * T qb := collarCKTaylorPackage_mul _ _ r qb s hr hqb hs
  have hconst : T s = MvPowerSeries.C M := by
    apply (hsame _ s (c M) hs (hasFPowerSeriesAt_const.congr
      (Filter.Eventually.mono heq (fun _ hz ↦ hz.symm)))).trans
    exact hc M
  rw [hS, hR, hplus, hTa, hTb] at hconst
  exact hconst

/-- The original majorant parameters give the same analytic scalar majorant with its exact
native rational formal PDE. Source: Gantumur, Theorem 18, equations 47–51. Call the accepted
prepared construction once; keep its same radius, function and genuine Taylor witness, with
all coefficient signs and actual zero value/first jet consequences. Transport its true cleared
coordinate PDE by the accepted scalar Taylor calculus. Both formal denominators have constant
one, so the accepted native equation equivalence gives the rational substitution PDE. This
discharges the formal PDE from original parameters rather than assuming it as an extra input. -/
theorem collarCKGoursat_taylor_formal (n m : ℕ) (hm : 0 < m)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧
      ∃ (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
        (p : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ),
        AnalyticAt ℝ U 0 ∧
        HasFPowerSeriesAt (U ∘ collarCKFullCoordinates) p 0 ∧
        (∀ d, 0 ≤ collarCKTaylorCoeff p d) ∧ collarCKTaylorCoeff p 0 = 0 ∧
        (∀ i, collarCKTaylorCoeff p (Finsupp.single i 1) = 0) ∧
        MvPowerSeries.HasSubst (collarCKGoursatSlots (m := m)
          (fun d ↦ collarCKTaylorCoeff p d)) ∧
        (MvPowerSeries.pderiv (Sum.inl ())
          (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries (CollarCKFullIndex n) ℝ) =
          MvPowerSeries.subst (collarCKGoursatSlots (m := m)
            (fun d ↦ collarCKTaylorCoeff p d)) (collarCKGoursatRHS n m M R rho)) := by
  obtain ⟨rho, hrho, hrho1, U, p, qt, qa, qb, hU, hp, hpos, hp0, hp1,
    hslots, hqt, hqa, hqb, heq⟩ := collarCKGoursat_taylor_prepared n m hm M R hM hR
  refine ⟨rho, hrho, hrho1, U, p, hU, hp, hpos, hp0, hp1, hslots, ?_⟩
  apply (collarCKGoursatRHS_equation_iff (m := m) M R rho
    (fun d ↦ collarCKTaylorCoeff p d) hp0 hp1).mpr
  exact collarCKGoursat_cleared_formalPDE M R rho U p qt qa qb hp hqt hqa hqb heq

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKGoursat_cleared_formalPDE

#print axioms GlobalEmbedding.Paper.collarCKGoursat_taylor_formal
