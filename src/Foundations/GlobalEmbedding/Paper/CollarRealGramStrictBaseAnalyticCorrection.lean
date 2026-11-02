import GlobalEmbedding.Paper.CollarQuadraticBallPersistence
import GlobalEmbedding.Paper.CollarRealGramNativeAnalyticCorrection

/-!
# Actual Gram-source analytic corrections from strict original base-point estimates

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 522–534. Nearby original real ball contraction is constructed, not supplied.
-/

open Set Filter WithLp Matrix
open scoped Topology NNReal Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual source Gram data and strict original real norm estimates only at the base point
construct the original real small-ball correction, exact source identities, ball uniqueness
and native joint analytic order omega on the same actual open base domain and original torus.

Source: Proposition `prop:collar`, proof lines 522–534. Construct the genuine periodic analytic
Gram coefficient, forcing and multiplier as in the actual source-native theorem. Their real
norm AnalyticAt gives continuity of the actual multiplier family and actual half-forcing.
The strict two base-point scalar bounds persist nearby and imply the actual original real ball
invariance and Lipschitz q on that whole ball, with the same radius and specified q<1. Applying
the already proved native source theorem yields its full equation, exact source lifts,
uniqueness and native analytic conclusions without a nearby-ball hypothesis. No source-Q
construction, geometric T_F/metric-defect construction or numerical base bounds are silently
proved here; these precise base estimates remain inputs. No complex-space contraction norm or
changed real little-space norm is introduced, and no final bundle gluing is claimed. -/
theorem collar_real_gram_strict_base_analytic_correction {b a M N : ℕ}
    (T : (Fin (b + a) → ℝ) → Matrix (Fin M) (Fin N) ℝ)
    (fH : (Fin (b + a) → ℝ) → (Fin M → ℝ))
    (V : Set (Fin b → ℝ)) (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hT : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ i j, AnalyticAt ℝ (fun z ↦ T z i j) x)
    (hfH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ fH x)
    (hperiodT : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        T (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = T x)
    (hperiodH : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        fH (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = fH x)
    (hbase : ∀ y : Fin a → ℝ,
      (T (Fin.append p₀ y) * (T (Fin.append p₀ y))ᵀ).det ≠ 0)
    (Q : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ))
    (hQτ : ∀ (h : EuclideanSpace ℝ (Fin a))
      (u v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)),
      Q (littlePeriodicCAlphaTranslateIsometry h u) (littlePeriodicCAlphaTranslateIsometry h v) =
        littlePeriodicCAlphaTranslateIsometry h (Q u v)) :
    let C := fun x ↦ (T x)ᵀ * (T x * (T x)ᵀ)⁻¹
    let fA := fun x (q : Fin (N * M)) ↦
      C x (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
    let qNorm := ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
      (F := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ)) Q
    ∃ V₀ : Set (Fin b → ℝ), IsOpen V₀ ∧ p₀ ∈ V₀ ∧ V₀ ⊆ V ∧
      (∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V₀ →
        (T x * (T x)ᵀ).det ≠ 0 ∧ T x * C x = 1) ∧
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
        (‖mult (AR p₀R) ((1 / 2 : ℝ) • HR p₀R)‖ +
          ‖mult (AR p₀R)‖ * qNorm * ρ ^ 2 < ρ) →
        (2 * ‖mult (AR p₀R)‖ * qNorm * ρ < (q : ℝ)) →
        ∃ (u : EuclideanSpace ℝ (Fin b) → LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
          (W : Set (EuclideanSpace ℝ (Fin b))), IsOpen W ∧ toLp 2 p₀ ∈ W ∧
          (∀ p ∈ W, ofLp p ∈ V₀ ∧
            (∀ y : EuclideanSpace ℝ (Fin a),
              (AR (collarRealJointParameter b a (p, 0))).val.toFun y =
                toLp 2 (fA (Fin.append (ofLp p) (ofLp y)))) ∧
            (∀ y : EuclideanSpace ℝ (Fin a),
              (HR (collarRealJointParameter b a (p, 0))).val.toFun y =
                toLp 2 (fH (Fin.append (ofLp p) (ofLp y)))) ∧
            ‖u p‖ ≤ ρ ∧
            mult (AR (collarRealJointParameter b a (p, 0)))
              ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q (u p) (u p)) = u p ∧
            ∀ v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖v‖ ≤ ρ →
              (mult (AR (collarRealJointParameter b a (p, 0)))
                ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q v v) = v ↔ u p = v)) ∧
          let _charted := periodicFlatTorusChartedSpace a
          ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin b))).prod
            (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ω
            (fun z : EuclideanSpace ℝ (Fin b) × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
              littlePeriodicCAlphaTorusValue (u z.1) z.2) (W ×ˢ univ) := by
  dsimp only
  obtain ⟨V₀, hV₀, hpV₀, hsub, hright, AR, HR, mult, hAR, hHR, hsource, hmult, hbranch⟩ :=
    collar_real_gram_native_analytic_correction T fH V hV p₀ hp₀ hT hfH
      hperiodT hperiodH hbase Q hQτ
  refine ⟨V₀, hV₀, hpV₀, hsub, hright, AR, HR, mult, hAR, hHR, hsource, hmult, ?_⟩
  intro ρ hρ q hq himage hlip
  apply hbranch ρ hρ q hq
  let A := fun p ↦ mult (AR p)
  let f := fun p ↦ mult (AR p) ((1 / 2 : ℝ) • HR p)
  have hA : ContinuousAt A _ := mult.continuous.continuousAt.comp' hAR.continuousAt
  have hf : ContinuousAt f _ := hA.clm_apply (hHR.continuousAt.const_smul (1 / 2 : ℝ))
  have hpersist := collar_quadratic_ball_persistence
    (X := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
    (Y := LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ)) A f Q _ hA hf ρ hρ q himage hlip
  filter_upwards [hpersist] with p hp
  simpa only [A, f, map_add] using hp

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_real_gram_strict_base_analytic_correction
