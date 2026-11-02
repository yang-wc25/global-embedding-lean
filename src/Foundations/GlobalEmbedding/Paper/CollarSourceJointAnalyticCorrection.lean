import GlobalEmbedding.Paper.CollarSourceAnalyticFixedPoints
import GlobalEmbedding.Paper.CollarSourceHolderTranslationIdentity
import GlobalEmbedding.Paper.CollarTranslationJointAnalytic
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation
import GlobalEmbedding.Paper.LittlePeriodicCAlphaMultiplierTranslate
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateFixedEquation

/-!
# Actual jointly real analytic source correction in base and orbit variables

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The actual translation identity follows from original small-ball uniqueness.
-/

open Set Filter WithLp
open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Actual real analytic periodic source coefficients and an actual bounded real shift-equivariant
Q give an actual correction jointly real analytic in the original base and orbit coordinates,
whenever the original real norm ball is invariant and uniformly contracting.

Source: Proposition `prop:collar`, proof lines 530–534. Construct the actual source analytic
fixed-point family and recover its actual original real little-space values by the proved real
coordinate CLM. Exact source lift formulas give actual coefficient/forcing shift identities.
The proved actual multiplier conjugation and translated fixed-equation theorem show that the
translated base solution solves the translated source equation. Actual translation preserves
its original norm, so the translated point remains in the same ball. Original real-ball
uniqueness identifies it with the translated-parameter solution. Compose the actual analytic
Banach family with the actual real parameter inclusion and actual bounded point evaluation;
this genuine translation identity gives joint real analyticity in the original coordinates.
No coefficient complex extension, real Holder membership, correction shift identity, function
space evaluation bound or joint source-function analyticity is an input. Source construction
of the actual bounded real Q, its shift equivariance and original small-ball estimates remains
explicit; no Schauder/source-Q or global bundle gluing is claimed constructed here. -/
theorem collar_source_joint_analytic_correction {b a M N : ℕ}
    (fA : (Fin (b + a) → ℝ) → (Fin (N * M) → ℝ))
    (fH : (Fin (b + a) → ℝ) → (Fin M → ℝ))
    (V : Set (Fin b → ℝ)) (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hfA : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ fA x)
    (hfH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ fH x)
    (hperiodA : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        fA (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = fA x)
    (hperiodH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        fH (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = fH x)
    (Q : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ))
    (hQτ : ∀ (h : EuclideanSpace ℝ (Fin a))
      (u v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)),
      Q (littlePeriodicCAlphaTranslateIsometry h u) (littlePeriodicCAlphaTranslateIsometry h v) =
        littlePeriodicCAlphaTranslateIsometry h (Q u v)) :
    let p₀R := collarEuclideanRealEquiv (b + a)
      (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
    ∃ (AR : collarEuclideanRealSubmodule (b + a) →
        LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ))
      (HR : collarEuclideanRealSubmodule (b + a) →
        LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ))
      (mult : LittlePeriodicCAlphaFunction a (N * M) 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)),
      AnalyticAt ℝ AR p₀R ∧ AnalyticAt ℝ HR p₀R ∧
      (∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
        (∀ y : EuclideanSpace ℝ (Fin a), (AR p).val.toFun y =
          toLp 2 (fun l ↦ fA
            (Fin.append (fun i : Fin b ↦ (p.val (Fin.castAdd a i)).re)
              (fun j : Fin a ↦ y j + (p.val (Fin.natAdd b j)).re)) l)) ∧
        (∀ y : EuclideanSpace ℝ (Fin a), (HR p).val.toFun y =
          toLp 2 (fun l ↦ fH
            (Fin.append (fun i : Fin b ↦ (p.val (Fin.castAdd a i)).re)
              (fun j : Fin a ↦ y j + (p.val (Fin.natAdd b j)).re)) l))) ∧
      (∀ coeff u y, (mult coeff u).val.toFun y =
        hilbertSchmidtCoordinateEvaluation M N (coeff.val.toFun y) (u.val.toFun y)) ∧
      ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (q : ℝ≥0), (q : ℝ) < 1 →
        (∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
          let S : Set (LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)) := {x | ‖x‖ ≤ ρ}
          let Φ := fun x ↦ mult (AR p) ((1 / 2 : ℝ) • HR p + Q x x)
          MapsTo Φ S S ∧ LipschitzOnWith q Φ S) →
        ∃ u : EuclideanSpace ℝ (Fin b) → LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ),
          (∀ᶠ p : EuclideanSpace ℝ (Fin b) in 𝓝 (toLp 2 p₀), ‖u p‖ ≤ ρ ∧
            mult (AR (collarRealJointParameter b a (p, 0)))
              ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q (u p) (u p)) = u p ∧
            ∀ v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖v‖ ≤ ρ →
              (mult (AR (collarRealJointParameter b a (p, 0)))
                ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q v v) = v ↔ u p = v)) ∧
          ∀ y₀ : EuclideanSpace ℝ (Fin a),
            AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a) ↦
              (u z.1).val.toFun z.2) (toLp 2 p₀, y₀) := by
  dsimp only
  let p₀R := collarEuclideanRealEquiv (b + a)
    (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
  obtain ⟨AR, HR, mult, hAR, hHR, hsource, hmult, hbranch⟩ :=
    collar_source_analytic_fixed_points fA fH V hV p₀ hp₀ hfA hfH hperiodA hperiodH Q
  refine ⟨AR, HR, mult, hAR, hHR, hsource, hmult, ?_⟩
  intro ρ hρ q hq hnear
  obtain ⟨ψ, hψ, hψnear⟩ := hbranch ρ hρ q hq hnear
  obtain ⟨_, r, _, _, hr, _, _, _, _, _⟩ :=
    collar_complex_holder_real_form (a := a) (N := N) (k := 2) (α := (1 / 2 : ℝ))
  let U (p : collarEuclideanRealSubmodule (b + a)) := r (ψ p.val)
  let Φ (p : collarEuclideanRealSubmodule (b + a))
      (v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)) :=
    mult (AR p) ((1 / 2 : ℝ) • HR p + Q v v)
  have hUnear : ∀ᶠ p : collarEuclideanRealSubmodule (b + a) in 𝓝 p₀R,
      ‖U p‖ ≤ ρ ∧ Φ p (U p) = U p ∧
      (∀ y, collarComplexHolderFunction (ψ p.val) y =
        toLp 2 (fun l ↦ (((U p).val.toFun y l : ℝ) : ℂ))) ∧
      (∀ v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖v‖ ≤ ρ →
        (Φ p v = v ↔ U p = v)) := by
    filter_upwards [hψnear] with p hp
    obtain ⟨v, hvnorm, hvfix, hψv, hvunique⟩ := hp
    have hUv : U p = v := by
      apply Subtype.ext
      apply periodicCAlpha_toFun_injective
      funext y
      change (r (ψ p.val)).val.toFun y = v.val.toFun y
      rw [hr, hψv]
      ext i
      exact Complex.ofReal_re _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hUv] using hvnorm
    · simpa only [Φ, hUv] using hvfix
    · intro y
      simpa only [hUv] using hψv y
    · intro w hw
      simpa only [Φ, hUv] using hvunique w hw
  let J := collarRealJointParameter b a
  have hJ₀ : J (toLp 2 p₀, 0) = p₀R := collar_real_joint_parameter_basepoint p₀
  have hτA := collar_source_holder_translation_identity fA p₀ AR
    (hsource.mono (fun p hp ↦ hp.1))
  have hτH := collar_source_holder_translation_identity fH p₀ HR
    (hsource.mono (fun p hp ↦ hp.2))
  have hJt := J.continuous.tendsto (toLp 2 p₀, 0)
  rw [hJ₀] at hJt
  have hbasecont : Continuous (fun z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a) ↦
      J (z.1, 0)) := J.continuous.comp (continuous_fst.prodMk continuous_const)
  have hbaset := hbasecont.tendsto (toLp 2 p₀, 0)
  rw [hJ₀] at hbaset
  have hUshift : ∀ᶠ z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a) in
      𝓝 (toLp 2 p₀, 0), U (J z) =
        littlePeriodicCAlphaTranslateIsometry z.2 (U (J (z.1, 0))) := by
    filter_upwards [hτA, hτH, hJt.eventually hUnear, hbaset.eventually hUnear]
      with z hzA hzH hz hz₀
    have hcoef := littlePeriodicCAlpha_multiplier_translate mult hmult (AR (J (z.1, 0))) z.2
    rw [← hzA] at hcoef
    have hcancel : littlePeriodicCAlphaTranslateIsometry (-z.2)
        ((1 / 2 : ℝ) • HR (J z)) = (1 / 2 : ℝ) • HR (J (z.1, 0)) := by
      rw [hzH, map_smul]
      have he := littlePeriodicCAlpha_translate_inverse (-z.2) (HR (J (z.1, 0)))
      rw [neg_neg] at he
      rw [he]
    have hforce : littlePeriodicCAlphaTranslateIsometry z.2
        (mult (AR (J (z.1, 0))) ((1 / 2 : ℝ) • HR (J (z.1, 0)))) =
          mult (AR (J z)) ((1 / 2 : ℝ) • HR (J z)) := by
      have he := congrArg (fun A : LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ) →L[ℝ]
          LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) ↦ A ((1 / 2 : ℝ) • HR (J z))) hcoef
      change littlePeriodicCAlphaTranslateIsometry z.2
        (mult (AR (J (z.1, 0))) (littlePeriodicCAlphaTranslateIsometry (-z.2)
          ((1 / 2 : ℝ) • HR (J z)))) = _ at he
      rw [hcancel] at he
      exact he
    have hfixed₀ : U (J (z.1, 0)) =
        mult (AR (J (z.1, 0))) ((1 / 2 : ℝ) • HR (J (z.1, 0))) +
          mult (AR (J (z.1, 0))) (Q (U (J (z.1, 0))) (U (J (z.1, 0)))) := by
      have he := hz₀.2.1
      change mult (AR (J (z.1, 0)))
        ((1 / 2 : ℝ) • HR (J (z.1, 0)) + Q (U (J (z.1, 0))) (U (J (z.1, 0)))) = _ at he
      rw [map_add] at he
      exact he.symm
    have htranslated := littlePeriodicCAlpha_translate_fixed_equation Q hQτ
      (mult (AR (J (z.1, 0)))) (mult (AR (J (z.1, 0))) ((1 / 2 : ℝ) • HR (J (z.1, 0))))
      (U (J (z.1, 0))) z.2 hfixed₀
    dsimp only at htranslated
    rw [hcoef, hforce] at htranslated
    have hfixedτ : Φ (J z)
        (littlePeriodicCAlphaTranslateIsometry z.2 (U (J (z.1, 0)))) =
          littlePeriodicCAlphaTranslateIsometry z.2 (U (J (z.1, 0))) := by
      change mult (AR (J z)) ((1 / 2 : ℝ) • HR (J z) +
        Q (littlePeriodicCAlphaTranslateIsometry z.2 (U (J (z.1, 0))))
          (littlePeriodicCAlphaTranslateIsometry z.2 (U (J (z.1, 0))))) = _
      rw [map_add]
      exact htranslated.symm
    have hnormτ : ‖littlePeriodicCAlphaTranslateIsometry z.2 (U (J (z.1, 0)))‖ ≤ ρ := by
      simpa only [LinearIsometry.norm_map] using hz₀.1
    exact (hz.2.2.2 _ hnormτ).mp hfixedτ
  let u (p : EuclideanSpace ℝ (Fin b)) := U (J (p, 0))
  refine ⟨u, ?_, ?_⟩
  · have hc : Continuous (fun p : EuclideanSpace ℝ (Fin b) ↦ J (p, 0)) :=
      J.continuous.comp (continuous_id.prodMk continuous_const)
    have ht := hc.tendsto (toLp 2 p₀)
    rw [hJ₀] at ht
    filter_upwards [ht.eventually hUnear] with p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.2⟩
  · intro y₀
    obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation
      (a := a) (N := N) (k := 2) (α := (1 / 2 : ℝ)) y₀
    let JC := (collarEuclideanRealSubmodule (b + a)).subtypeL.comp J
    have hψJ : AnalyticAt ℂ ψ (JC (toLp 2 p₀, 0)) := by
      change AnalyticAt ℂ ψ (J (toLp 2 p₀, 0)).val
      rw [hJ₀]
      exact hψ
    have htranslation : ∀ᶠ z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a) in
        𝓝 (toLp 2 p₀, 0), (ev.comp r) (ψ (JC z)) = (u z.1).val.toFun (y₀ + z.2) := by
      filter_upwards [hUshift] with z hz
      change ev (U (J z)) = (u z.1).val.toFun (y₀ + z.2)
      rw [hev, hz]
      rfl
    exact collar_translation_joint_analytic ψ JC (ev.comp r)
      (fun z : EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin a) ↦
        (u z.1).val.toFun z.2) (toLp 2 p₀) y₀ hψJ htranslation

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_source_joint_analytic_correction
