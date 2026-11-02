import GlobalEmbedding.Paper.CollarCKGoursatTaylorPositive
import GlobalEmbedding.Paper.CollarCKGoursatFormalRHS

/-!
# The complete analytic side of the same Goursat Taylor bridge

Source: Gantumur, notes2, Theorem 18, equations 47–51.
These seven existing proofs are extracted unchanged from the successful parent checkpoint.
They construct the same actual majorant and all analytic factor witnesses, lawful full-origin
slots and the actual cleared coordinate PDE from the original majorant parameters.
The final formal PDE remains a separate parent obligation requiring the sole shared calculus.
-/

noncomputable section
open scoped BigOperators Topology
namespace GlobalEmbedding.Paper

/-- Clear the denominators of the same actual near-origin Goursat PDE lawfully.
Source: Gantumur, Theorem 18. Both actual denominators are continuous near the origin and
equal one there, using the actual zero value and first jet. They are therefore nonzero on
one neighborhood. Adding `M` and multiplying the actual rational identity gives the polynomial
identity on that neighborhood, without any formal PDE premise. -/
theorem collarCKGoursat_cleared_actualPDE {n m : ℕ} (M R rho : ℝ)
    (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (hU : AnalyticAt ℝ U 0) (hU0 : U 0 = 0) (hD0 : fderiv ℝ U 0 = 0)
    (heq : ∀ᶠ z in 𝓝 0, fderiv ℝ U z (1, 0) =
      M / ((1 - ((∑ i, z.2 i) + z.1 / rho + (m : ℝ) * U z) / R) *
        (1 - (∑ i : Fin n, ∑ _j : Fin m,
          fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R)) - M) :
    ∀ᶠ z in 𝓝 0, (fderiv ℝ U z (1, 0) + M) *
      (1 - ((∑ i, z.2 i) + z.1 / rho + (m : ℝ) * U z) / R) *
      (1 - (∑ i : Fin n, ∑ _j : Fin m,
        fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R) = M := by
  let A := fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦
    1 - ((∑ i, z.2 i) + z.1 / rho + (m : ℝ) * U z) / R
  let B := fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦
    1 - (∑ i : Fin n, ∑ _j : Fin m,
      fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R
  have hAc : ContinuousAt A 0 := by
    have hc := hU.continuousAt
    fun_prop
  have hBc : ContinuousAt B 0 := by
    have hc := hU.fderiv.continuousAt
    fun_prop
  have hA0 : A 0 = 1 := by simp [A, hU0]
  have hB0 : B 0 = 1 := by simp [B, hD0]
  have hAe : ∀ᶠ z in 𝓝 0, A z ≠ 0 := hAc.eventually_ne (by simp [hA0])
  have hBe : ∀ᶠ z in 𝓝 0, B z ≠ 0 := hBc.eventually_ne (by simp [hB0])
  filter_upwards [heq, hAe, hBe] with z hz hAz hBz
  change (fderiv ℝ U z (1, 0) + M) * A z * B z = M
  have htime : fderiv ℝ U z (1, 0) + M = M / (A z * B z) := by
    dsimp only [A, B]
    linarith
  rw [htime, mul_assoc, div_mul_cancel₀ _ (mul_ne_zero hAz hBz)]

/-- The literal full-coordinate time basis vector is the original native normal direction.
Source: Gantumur, Theorem 18, normal coordinate convention. -/
theorem collarCKFullCoordinates_time {n : ℕ} :
    collarCKFullCoordinates (Pi.single (Sum.inl ()) (1 : ℝ)) =
      ((1, 0) : ℝ × EuclideanSpace ℝ (Fin n)) := by
  apply Prod.ext
  · rfl
  · ext i
    change (Pi.single (Sum.inl ()) (1 : ℝ) : CollarCKFullIndex n → ℝ) (Sum.inr i) = 0
    simp

/-- The literal full-coordinate spatial basis vector is the original native Euclidean direction.
Source: Gantumur, Theorem 18, spatial coordinate convention. -/
theorem collarCKFullCoordinates_spatial {n : ℕ} (i : Fin n) :
    collarCKFullCoordinates (Pi.single (Sum.inr i) (1 : ℝ)) =
      ((0, EuclideanSpace.single i 1) : ℝ × EuclideanSpace ℝ (Fin n)) := by
  apply Prod.ext
  · change (Pi.single (Sum.inr i) (1 : ℝ) : CollarCKFullIndex n → ℝ) (Sum.inl ()) = 0
    simp
  · ext j
    change (Pi.single (Sum.inr i) (1 : ℝ) : CollarCKFullIndex n → ℝ) (Sum.inr j) =
      (EuclideanSpace.single i 1) j
    simp [EuclideanSpace.single, Pi.single_apply]

/-- The actual coordinate partial derivatives of the same function match its original directions.
Source: Gantumur, Theorem 18. Pull the analytic neighborhood back through the canonical
continuous linear coordinates and apply the actual Fréchet chain rule at every point there. -/
theorem collarCKGoursat_coordinate_derivatives {n : ℕ}
    (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ) (hU : AnalyticAt ℝ U 0) :
    ∀ᶠ z : CollarCKFullIndex n → ℝ in 𝓝 0,
      fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inl ()) 1) =
        fderiv ℝ U (collarCKFullCoordinates z) (1, 0) ∧
      ∀ i, fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1) =
        fderiv ℝ U (collarCKFullCoordinates z) (0, EuclideanSpace.single i 1) := by
  have hL : Filter.Tendsto (collarCKFullCoordinates (n := n)) (𝓝 0) (𝓝 0) := by
    have ht : Filter.Tendsto (collarCKFullCoordinates (n := n)) (𝓝 0)
        (𝓝 (collarCKFullCoordinates 0)) := collarCKFullCoordinates.continuous.continuousAt
    simpa only [map_zero] using ht
  filter_upwards [hL.eventually hU.eventually_analyticAt] with z hz
  have hd := (hz.differentiableAt.hasFDerivAt.comp z
    collarCKFullCoordinates.hasFDerivAt).fderiv
  rw [hd]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    collarCKFullCoordinates_time, collarCKFullCoordinates_spatial]

/-- The same actual cleared PDE in exactly the shared full-coordinate convention.
Source: Gantumur, Theorem 18. Compose the proved actual cleared identity with the canonical
linear coordinates, replace actual partial derivatives by the native chain-rule identities,
and write division as multiplication by the same real inverses. -/
theorem collarCKGoursat_cleared_coordinatePDE {n m : ℕ} (M R rho : ℝ)
    (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
    (hU : AnalyticAt ℝ U 0) (hU0 : U 0 = 0) (hD0 : fderiv ℝ U 0 = 0)
    (heq : ∀ᶠ z in 𝓝 0, fderiv ℝ U z (1, 0) =
      M / ((1 - ((∑ i, z.2 i) + z.1 / rho + (m : ℝ) * U z) / R) *
        (1 - (∑ i : Fin n, ∑ _j : Fin m,
          fderiv ℝ U z (0, EuclideanSpace.single i 1)) / R)) - M) :
    ∀ᶠ z : CollarCKFullIndex n → ℝ in 𝓝 0,
      (fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inl ()) 1) + M) *
        (1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) + rho⁻¹ * z (Sum.inl ()) +
          (∑ _j : Fin m, U (collarCKFullCoordinates z)))) *
        (1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
          fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1))) = M := by
  have hL : Filter.Tendsto (collarCKFullCoordinates (n := n)) (𝓝 0) (𝓝 0) := by
    have ht : Filter.Tendsto (collarCKFullCoordinates (n := n)) (𝓝 0)
        (𝓝 (collarCKFullCoordinates 0)) := collarCKFullCoordinates.continuous.continuousAt
    simpa only [map_zero] using ht
  filter_upwards [hL.eventually (collarCKGoursat_cleared_actualPDE M R rho U
    hU hU0 hD0 heq), collarCKGoursat_coordinate_derivatives U hU] with z hz hpartial
  rw [hpartial.1]
  simp_rw [hpartial.2]
  have hfirst : (1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) + rho⁻¹ * z (Sum.inl ()) +
      (∑ _j : Fin m, U (collarCKFullCoordinates z)))) =
      1 - ((∑ i, (collarCKFullCoordinates z).2 i) +
        (collarCKFullCoordinates z).1 / rho + (m : ℝ) * U (collarCKFullCoordinates z)) / R := by
    change (1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) + rho⁻¹ * z (Sum.inl ()) +
      (∑ _j : Fin m, U (collarCKFullCoordinates z)))) =
      1 - ((∑ i : Fin n, z (Sum.inr i)) + z (Sum.inl ()) / rho +
        (m : ℝ) * U (collarCKFullCoordinates z)) / R
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      div_eq_mul_inv]
    ring
  rw [hfirst]
  convert hz using 1; ring

/-- All factors of the same cleared coordinate PDE have genuine analytic expansions.
Source: Gantumur, Theorem 18. Compose the actual analytic majorant with the existing coordinates,
use native analyticity of its Fréchet derivative and evaluation, and take finite sums and scalar
products for the two literal denominators. The expansions are constructed from analyticity;
they are not supplied as desired Taylor identities or solutions. -/
theorem collarCKGoursat_factor_expansions {n : ℕ} (m : ℕ) (R rho : ℝ)
    (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ) (hU : AnalyticAt ℝ U 0) :
    ∃ qt qa qb : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ,
      HasFPowerSeriesAt
        (fun z ↦ fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inl ()) 1))
        qt 0 ∧
      HasFPowerSeriesAt (fun z ↦ 1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) +
        rho⁻¹ * z (Sum.inl ()) + (∑ _j : Fin m, U (collarCKFullCoordinates z)))) qa 0 ∧
      HasFPowerSeriesAt (fun z ↦ 1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
        fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1))) qb 0 := by
  have hf : AnalyticAt ℝ (U ∘ collarCKFullCoordinates) 0 :=
    hU.comp_of_eq (collarCKFullCoordinates.toContinuousLinearMap.analyticAt 0) (map_zero _)
  have hpartial (i : CollarCKFullIndex n) : AnalyticAt ℝ
      (fun z ↦ fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single i 1)) 0 :=
    ((ContinuousLinearMap.apply ℝ ℝ
      (Pi.single i (1 : ℝ) : CollarCKFullIndex n → ℝ)).analyticAt _).comp hf.fderiv
  have hx : AnalyticAt ℝ (fun z : CollarCKFullIndex n → ℝ ↦ ∑ i : Fin n, z (Sum.inr i))
      0 := Finset.univ.analyticAt_fun_sum (fun (i : Fin n) _ ↦
        (ContinuousLinearMap.proj (R := ℝ) (Sum.inr i) :
          (CollarCKFullIndex n → ℝ) →L[ℝ] ℝ).analyticAt 0)
  have ht : AnalyticAt ℝ (fun z : CollarCKFullIndex n → ℝ ↦ z (Sum.inl ())) 0 :=
    (ContinuousLinearMap.proj (R := ℝ) (Sum.inl ()) :
      (CollarCKFullIndex n → ℝ) →L[ℝ] ℝ).analyticAt 0
  have hv : AnalyticAt ℝ (fun z ↦ ∑ _j : Fin m, U (collarCKFullCoordinates z)) 0 :=
    Finset.univ.analyticAt_fun_sum (fun _ _ ↦ hf)
  have ha : AnalyticAt ℝ (fun z : CollarCKFullIndex n → ℝ ↦
      1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) + rho⁻¹ * z (Sum.inl ()) +
        (∑ _j : Fin m, U (collarCKFullCoordinates z)))) 0 :=
    analyticAt_const.sub ((analyticAt_const (v := R⁻¹)).smul
      ((hx.add ((analyticAt_const (v := rho⁻¹)).smul ht)).add hv))
  have hb : AnalyticAt ℝ (fun z : CollarCKFullIndex n → ℝ ↦
      1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
        fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1))) 0 :=
    analyticAt_const.sub ((analyticAt_const (v := R⁻¹)).smul
      (Finset.univ.analyticAt_fun_sum (fun i _ ↦
        Finset.univ.analyticAt_fun_sum (fun _ _ ↦ hpartial (Sum.inr i)))))
  obtain ⟨qt, hqt⟩ := hpartial (Sum.inl ())
  obtain ⟨qa, hqa⟩ := ha
  obtain ⟨qb, hqb⟩ := hb
  exact ⟨qt, qa, qb, hqt, hqa, hqb⟩

/-- Original majorant parameters construct all same-function data for the remaining Taylor step.
Source: Gantumur, Theorem 18. Call the accepted positive-majorant constructor once, derive the
actual cleared coordinate PDE, construct genuine expansions of its three factors, and discharge
the full-origin substitution criterion from the actual zero value and first jet. The formal PDE
identity is still a separate conclusion to be derived by the shared Taylor calculus. -/
theorem collarCKGoursat_taylor_prepared (n m : ℕ) (hm : 0 < m)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧
      ∃ (U : ℝ × EuclideanSpace ℝ (Fin n) → ℝ)
        (p qt qa qb : FormalMultilinearSeries ℝ (CollarCKFullIndex n → ℝ) ℝ),
        AnalyticAt ℝ U 0 ∧
        HasFPowerSeriesAt (U ∘ collarCKFullCoordinates) p 0 ∧
        (∀ d, 0 ≤ collarCKTaylorCoeff p d) ∧ collarCKTaylorCoeff p 0 = 0 ∧
        (∀ i, collarCKTaylorCoeff p (Finsupp.single i 1) = 0) ∧
        MvPowerSeries.HasSubst (collarCKGoursatSlots (m := m)
          (fun d ↦ collarCKTaylorCoeff p d)) ∧
        HasFPowerSeriesAt
          (fun z ↦ fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inl ()) 1))
          qt 0 ∧
        HasFPowerSeriesAt (fun z ↦ 1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) +
          rho⁻¹ * z (Sum.inl ()) + (∑ _j : Fin m, U (collarCKFullCoordinates z)))) qa 0 ∧
        HasFPowerSeriesAt (fun z ↦ 1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
          fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1))) qb 0 ∧
        (∀ᶠ z : CollarCKFullIndex n → ℝ in 𝓝 0,
          (fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inl ()) 1) + M) *
            (1 - R⁻¹ * ((∑ i : Fin n, z (Sum.inr i)) + rho⁻¹ * z (Sum.inl ()) +
              (∑ _j : Fin m, U (collarCKFullCoordinates z)))) *
            (1 - R⁻¹ * (∑ i : Fin n, ∑ _j : Fin m,
              fderiv ℝ (U ∘ collarCKFullCoordinates) z (Pi.single (Sum.inr i) 1))) = M) := by
  obtain ⟨rho, hrho, hrho1, U, p, hU0, hU, hD0, heq, hp, hpos, hp0, hp1⟩ :=
    collarCKGoursat_taylor_positive n m hm M R hM hR
  obtain ⟨qt, qa, qb, hqt, hqa, hqb⟩ := collarCKGoursat_factor_expansions m R rho U hU
  have hsingle (i : CollarCKFullIndex n) :
      collarCKTaylorCoeff p (Finsupp.single i 1) = 0 :=
    hp1 _ (Finsupp.degree_single _ _)
  have hslots : MvPowerSeries.HasSubst (collarCKGoursatSlots (m := m)
      (fun d ↦ collarCKTaylorCoeff p d)) :=
    collarCKGoursatSlots_hasSubst _ hp0 hsingle
  exact ⟨rho, hrho, hrho1, U, p, qt, qa, qb, hU, hp, hpos, hp0, hsingle, hslots,
    hqt, hqa, hqb, collarCKGoursat_cleared_coordinatePDE M R rho U hU hU0 hD0 heq⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKGoursat_cleared_actualPDE
#print axioms GlobalEmbedding.Paper.collarCKFullCoordinates_time
#print axioms GlobalEmbedding.Paper.collarCKFullCoordinates_spatial
#print axioms GlobalEmbedding.Paper.collarCKGoursat_coordinate_derivatives
#print axioms GlobalEmbedding.Paper.collarCKGoursat_cleared_coordinatePDE
#print axioms GlobalEmbedding.Paper.collarCKGoursat_factor_expansions
#print axioms GlobalEmbedding.Paper.collarCKGoursat_taylor_prepared
