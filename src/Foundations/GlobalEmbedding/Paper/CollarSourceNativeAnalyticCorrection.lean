import GlobalEmbedding.Paper.CollarSourceJointAnalyticCorrection
import GlobalEmbedding.Paper.CollarHolderNativeJointAnalytic

/-!
# Actual source correction on one common base neighborhood and the original torus

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Original real small-ball solutions and genuine native analytic order omega.
-/

open Set Filter WithLp
open scoped Topology NNReal Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Real analytic periodic source coefficients and the actual real contraction construct the
original correction, original fixed equation and uniqueness, and native joint analyticity on
one common actual open base neighborhood times the original torus.

Source: Proposition `prop:collar`, proof lines 530–534. The proved source analytic fixed-point
and actual translation argument give actual little-space values whose lifts are joint analytic
at every point over the given base point. Actual periodic compactness provides one common base
ball; the actual torus lifting equivalence descends genuine analytic-order regularity there.
Pull the proved source coefficient formulas and original real-ball fixed equation back along
the actual zero-shift base inclusion. Intersect their actual open neighborhood with the analytic
ball and the original source base domain. All exact source, norm, equation and uniqueness claims
then hold throughout that same neighborhood. No complex extensions, Holder membership, analytic
operator families, torus values, charts or common analytic domain are assumed. The actual real
Q, its equivariance and real contraction estimates remain inputs; no source-Q construction,
Schauder estimate or global principal-bundle gluing is claimed. -/
theorem collar_source_native_analytic_correction {b a M N : ℕ}
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
        ∃ (u : EuclideanSpace ℝ (Fin b) → LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
          (W : Set (EuclideanSpace ℝ (Fin b))), IsOpen W ∧ toLp 2 p₀ ∈ W ∧
          (∀ p ∈ W, ofLp p ∈ V ∧
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
  let p₀R := collarEuclideanRealEquiv (b + a)
    (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
  obtain ⟨AR, HR, mult, hAR, hHR, hsource, hmult, hbranch⟩ :=
    collar_source_joint_analytic_correction fA fH V hV p₀ hp₀ hfA hfH hperiodA hperiodH Q hQτ
  refine ⟨AR, HR, mult, hAR, hHR, hsource, hmult, ?_⟩
  intro ρ hρ q hq hnear
  obtain ⟨u, hfixed, hjoint⟩ := hbranch ρ hρ q hq hnear
  obtain ⟨ε, hε, hnative⟩ := collar_holder_native_joint_analytic u (toLp 2 p₀) hjoint
  let J := collarRealJointParameter b a
  have hc : Continuous (fun p : EuclideanSpace ℝ (Fin b) ↦ J (p, 0)) :=
    J.continuous.comp (continuous_id.prodMk continuous_const)
  have ht := hc.tendsto (toLp 2 p₀)
  rw [collar_real_joint_parameter_basepoint] at ht
  have hVnear : ∀ᶠ p : EuclideanSpace ℝ (Fin b) in 𝓝 (toLp 2 p₀), ofLp p ∈ V :=
    (hV.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin b ↦ ℝ))).mem_nhds hp₀
  have hgood : ∀ᶠ p : EuclideanSpace ℝ (Fin b) in 𝓝 (toLp 2 p₀), ofLp p ∈ V ∧
      (∀ y : EuclideanSpace ℝ (Fin a), (AR (J (p, 0))).val.toFun y =
        toLp 2 (fA (Fin.append (ofLp p) (ofLp y)))) ∧
      (∀ y : EuclideanSpace ℝ (Fin a), (HR (J (p, 0))).val.toFun y =
        toLp 2 (fH (Fin.append (ofLp p) (ofLp y)))) ∧
      ‖u p‖ ≤ ρ ∧ mult (AR (J (p, 0)))
        ((1 / 2 : ℝ) • HR (J (p, 0)) + Q (u p) (u p)) = u p ∧
      (∀ v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖v‖ ≤ ρ →
        (mult (AR (J (p, 0))) ((1 / 2 : ℝ) • HR (J (p, 0)) + Q v v) = v ↔ u p = v)) := by
    filter_upwards [hVnear, ht.eventually hsource, hfixed] with p hpV hps hpfix
    refine ⟨hpV, ?_, ?_, hpfix⟩
    · intro y
      simpa only [J, collar_real_joint_parameter_base, collar_real_joint_parameter_shift,
        PiLp.zero_apply, add_zero] using hps.1 y
    · intro y
      simpa only [J, collar_real_joint_parameter_base, collar_real_joint_parameter_shift,
        PiLp.zero_apply, add_zero] using hps.2 y
  obtain ⟨W, hWgood, hWopen, hpW⟩ := eventually_nhds_iff.mp hgood
  refine ⟨u, W ∩ Metric.ball (toLp 2 p₀) ε, hWopen.inter Metric.isOpen_ball,
    ⟨hpW, Metric.mem_ball_self hε⟩, ?_, ?_⟩
  · intro p hp
    exact hWgood p hp.1
  · dsimp only at hnative ⊢
    let _charted := periodicFlatTorusChartedSpace a
    exact hnative.mono (fun z hz ↦ ⟨hz.1.2, hz.2⟩)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_source_native_analytic_correction
