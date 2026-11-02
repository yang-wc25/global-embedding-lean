import GlobalEmbedding.Paper.CollarHolderAnalyticRealFixedPoints
import GlobalEmbedding.Paper.CollarHolderMixedBilinearExtension
import GlobalEmbedding.Paper.BalancedHolderMultiplicationBounded
import GlobalEmbedding.Paper.HilbertSchmidtCoordinateEvaluationFormula

/-!
# Analytic extension of the fixed points on the original real little Hölder ball

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
equation (5.2), proof lines 524–534. The original real contraction constant is preserved.
-/

open Set Filter WithLp
open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Actual analytic coefficient extensions and the original real bounded Q construct an
analytic branch whose real values solve the original real contraction equation uniquely.

Source: Proposition `prop:collar`, equation (5.2), proof lines 524–534. Construct real matrix
multiplication from its proved actual Hölder bound. Complexify the fixed actual bounded real Q.
The actual real little space is isometric to the pointwise-real complex subspace. The exact
pointwise coefficient agreement and exact real multiplication formula conjugate the complex
right-hand side to the original real equation through that isometry. Hence original real ball
invariance and its actual Lipschitz q transfer with exactly the same q. Apply the actual
analytic Holder fixed-points theorem and transport the branch's real values back by the
isometry. Its equation and uniqueness are exactly the original real equation and norm ball.
No complex Q, complex contraction estimate or changed real norm is an input. Construction of
the paper's actual bounded real Q and original real small-ball estimates remains separate. -/
theorem collar_original_real_analytic_fixed_points
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℂ Z]
    [IsScalarTower ℝ ℂ Z] [CompleteSpace Z]
    {a M N k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (P : Submodule ℝ Z) (p₀ : P)
    (A : Z → CollarComplexHolderSpace a (N * M) k α)
    (H : Z → CollarComplexHolderSpace a M k α)
    (AR : P → LittlePeriodicCAlphaFunction a (N * M) k α)
    (HR : P → LittlePeriodicCAlphaFunction a M k α)
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a M k α)
    (hA : AnalyticAt ℂ A (p₀ : Z)) (hH : AnalyticAt ℂ H (p₀ : Z))
    (hmatch : ∀ᶠ p : P in 𝓝 p₀,
      (∀ y, collarComplexHolderFunction (A (p : Z)) y =
        toLp 2 (fun i ↦ (((AR p).val.toFun y i : ℝ) : ℂ))) ∧
      (∀ y, collarComplexHolderFunction (H (p : Z)) y =
        toLp 2 (fun i ↦ (((HR p).val.toFun y i : ℝ) : ℂ)))) :
    ∃ mult : LittlePeriodicCAlphaFunction a (N * M) k α →L[ℝ]
        LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α,
      (∀ coeff u y, (mult coeff u).val.toFun y =
        hilbertSchmidtCoordinateEvaluation M N (coeff.val.toFun y) (u.val.toFun y)) ∧
      ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (q : ℝ≥0), (q : ℝ) < 1 →
        (∀ᶠ p : P in 𝓝 p₀,
          let S : Set (LittlePeriodicCAlphaFunction a N k α) := {x | ‖x‖ ≤ ρ}
          let Φ := fun x ↦ mult (AR p) ((1 / 2 : ℝ) • HR p + Q x x)
          MapsTo Φ S S ∧ LipschitzOnWith q Φ S) →
        ∃ ψ : Z → CollarComplexHolderSpace a N k α, AnalyticAt ℂ ψ (p₀ : Z) ∧
          ∀ᶠ p : P in 𝓝 p₀,
            ∃ u : LittlePeriodicCAlphaFunction a N k α, ‖u‖ ≤ ρ ∧
              mult (AR p) ((1 / 2 : ℝ) • HR p + Q u u) = u ∧
              (∀ y, collarComplexHolderFunction (ψ (p : Z)) y =
                toLp 2 (fun i ↦ ((u.val.toFun y i : ℝ) : ℂ))) ∧
              (∀ v : LittlePeriodicCAlphaFunction a N k α, ‖v‖ ≤ ρ →
                (mult (AR p) ((1 / 2 : ℝ) • HR p + Q v v) = v ↔ u = v)) := by
  obtain ⟨_, _, mult, hmult, _⟩ :=
    balanced_holder_multiplication_bounded (a := a) (M := M) (N := N) (k := k) hα0 hα1
  obtain ⟨R, _, e, _, _, he, hmem, _, _, _⟩ :=
    collar_complex_holder_closed_real_form (a := a) (N := N) (k := k) (α := α)
  let J : LittlePeriodicCAlphaFunction a N k α →ₗᵢ[ℝ]
      CollarComplexHolderSpace a N k α := R.subtypeₗᵢ.comp e.toLinearIsometry
  have hJ (u : LittlePeriodicCAlphaFunction a N k α) (y : EuclideanSpace ℝ (Fin a)) :
      collarComplexHolderFunction (J u) y =
        toLp 2 (fun i ↦ ((u.val.toFun y i : ℝ) : ℂ)) := he u y
  have hJreal (u : LittlePeriodicCAlphaFunction a N k α) :
      ∀ y i, (collarComplexHolderFunction (J u) y i).im = 0 :=
    (hmem (J u)).mp (e u).property
  have hJdist (u v : LittlePeriodicCAlphaFunction a N k α) :
      dist (J u) (J v) = dist u v := J.isometry.dist_eq u v
  have hlift (x : CollarComplexHolderSpace a N k α)
      (hx : ∀ y i, (collarComplexHolderFunction x y i).im = 0) :
      ∃ u : LittlePeriodicCAlphaFunction a N k α, J u = x := by
    let xr : R := ⟨x, (hmem x).mpr hx⟩
    refine ⟨e.symm xr, ?_⟩
    change (e (e.symm xr) : CollarComplexHolderSpace a N k α) = x
    rw [e.apply_symm_apply]
  obtain ⟨j₁, j₂, jM, hj₁, hj₂, hjM, B, hB, _⟩ :=
    collar_holder_mixed_bilinear_extension Q
  have hj₁J (u : LittlePeriodicCAlphaFunction a N k α) : j₁ u = J u := by
    apply collarComplexHolderFunction_injective
    funext y
    rw [hj₁, hJ]
  have hj₂J (u : LittlePeriodicCAlphaFunction a N k α) : j₂ u = J u := by
    apply collarComplexHolderFunction_injective
    funext y
    rw [hj₂, hJ]
  have hBJ (u v : LittlePeriodicCAlphaFunction a N k α) : B (J u) (J v) = jM (Q u v) := by
    rw [← hj₁J, ← hj₂J]
    exact hB u v
  obtain ⟨C, hC, _, _, hbranch⟩ :=
    collar_holder_analytic_real_fixed_points hα0 hα1 P p₀ A H B hA hH
  have hhalf (v : LittlePeriodicCAlphaFunction a M k α) :
      (1 / 2 : ℂ) • jM v = jM ((1 / 2 : ℝ) • v) := by
    rw [map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    have hc : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    change (1 / 2 : ℂ) • jM v = ((1 / 2 : ℝ) : ℂ) • jM v
    rw [hc]
  let ΦR (p : P) (u : LittlePeriodicCAlphaFunction a N k α) :=
    mult (AR p) ((1 / 2 : ℝ) • HR p + Q u u)
  let ΦC (p : P) (u : CollarComplexHolderSpace a N k α) :=
    C (A (p : Z)) ((1 / 2 : ℂ) • H (p : Z) + B u u)
  have hconj (p : P)
      (hp : (∀ y, collarComplexHolderFunction (A (p : Z)) y =
        toLp 2 (fun i ↦ (((AR p).val.toFun y i : ℝ) : ℂ))) ∧
        (∀ y, collarComplexHolderFunction (H (p : Z)) y =
        toLp 2 (fun i ↦ (((HR p).val.toFun y i : ℝ) : ℂ))))
      (u : LittlePeriodicCAlphaFunction a N k α) : ΦC p (J u) = J (ΦR p u) := by
    have hHreal : H (p : Z) = jM (HR p) := by
      apply collarComplexHolderFunction_injective
      funext y
      rw [hp.2, hjM]
    have hprod (v : LittlePeriodicCAlphaFunction a M k α) :
        C (A (p : Z)) (jM v) = J (mult (AR p) v) := by
      apply collarComplexHolderFunction_injective
      funext y
      ext i
      rw [hC, hJ, hp.1, hjM]
      rw [hmult]
      change (∑ j : Fin M, (((AR p).val.toFun y (finProdFinEquiv (i, j)) : ℝ) : ℂ) *
        ((v.val.toFun y j : ℝ) : ℂ)) =
          (hilbertSchmidtCoordinateEvaluation M N ((AR p).val.toFun y) (v.val.toFun y) i : ℂ)
      rw [hilbertSchmidt_coordinate_evaluation_formula]
      simp
    change C (A (p : Z)) ((1 / 2 : ℂ) • H (p : Z) + B (J u) (J u)) = _
    rw [hHreal, hBJ, hhalf, ← jM.map_add]
    exact hprod _
  refine ⟨mult, hmult, ?_⟩
  intro ρ hρ q hq hnear
  let SC : Set (CollarComplexHolderSpace a N k α) :=
    {x | (∀ y i, (collarComplexHolderFunction x y i).im = 0) ∧ ‖x‖ ≤ ρ}
  have hnearC : ∀ᶠ p : P in 𝓝 p₀,
      MapsTo (ΦC p) SC SC ∧ LipschitzOnWith q (ΦC p) SC := by
    filter_upwards [hnear, hmatch] with p hp hm
    change MapsTo (ΦR p) {x | ‖x‖ ≤ ρ} {x | ‖x‖ ≤ ρ} ∧
      LipschitzOnWith q (ΦR p) {x | ‖x‖ ≤ ρ} at hp
    refine ⟨?_, ?_⟩
    · rintro x ⟨hxreal, hxnorm⟩
      obtain ⟨u, rfl⟩ := hlift x hxreal
      have hu : ‖u‖ ≤ ρ := by simpa only [J.norm_map] using hxnorm
      change (∀ y i, (collarComplexHolderFunction (ΦC p (J u)) y i).im = 0) ∧ _
      rw [hconj p hm]
      have hru : ‖ΦR p u‖ ≤ ρ := hp.1 hu
      exact ⟨hJreal _, by simpa only [J.norm_map] using hru⟩
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      obtain ⟨u, rfl⟩ := hlift x hx.1
      obtain ⟨v, rfl⟩ := hlift y hy.1
      have hu : ‖u‖ ≤ ρ := by simpa only [J.norm_map] using hx.2
      have hv : ‖v‖ ≤ ρ := by simpa only [J.norm_map] using hy.2
      simpa only [hconj p hm, hJdist] using hp.2.dist_le_mul u hu v hv
  obtain ⟨ψ, hψ, hψnear⟩ := hbranch ρ hρ q hq hnearC
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψnear, hmatch] with p hp hm
  change ψ (p : Z) ∈ SC ∧ ΦC p (ψ (p : Z)) = ψ (p : Z) ∧
    ∀ x ∈ SC, ΦC p x = x ↔ ψ (p : Z) = x at hp
  obtain ⟨u, hu⟩ := hlift (ψ (p : Z)) hp.1.1
  have hunorm : ‖u‖ ≤ ρ := by rw [← J.norm_map u, hu]; exact hp.1.2
  have hufix : ΦR p u = u := by
    apply J.injective
    rw [← hconj p hm, hu]
    exact hp.2.1
  refine ⟨u, hunorm, hufix, ?_, ?_⟩
  · intro y
    rw [← hu, hJ]
  · intro v hv
    constructor
    · intro hfix
      apply J.injective
      have hvC : ΦC p (J v) = J v := by rw [hconj p hm]; exact congrArg J hfix
      have hvSC : J v ∈ SC := ⟨hJreal v, by simpa only [J.norm_map] using hv⟩
      exact hu.trans ((hp.2.2 (J v) hvSC).mp hvC)
    · intro huv
      rw [← huv]
      exact hufix

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_original_real_analytic_fixed_points
