import GlobalEmbedding.Paper.CollarRealGramStrictBaseAnalyticCorrection
import GlobalEmbedding.Paper.CollarQuadraticBallPersistence

/-!
# Explicit small-forcing analytic corrections with an original norm estimate

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 522–534 and the small-ball estimate in Lemma `lem:balanced`, lines 403–410.
-/

open Set Filter WithLp Matrix
open scoped Topology NNReal Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual real Gram source data give explicit positive smallness threshold and ball radius.
Below that original forcing threshold, the actual correction is native joint analytic, uniquely
solves the original equation in that ball, and has an original norm bound linear in the forcing.

Source: Proposition `prop:collar`, proof lines 522–534 and Lemma `lem:balanced`, lines 403–410.
Let K=norm(A0) norm(Q), rho=1/(4(K+1)), delta=rho/(norm(A0)+1). Positivity is automatic and
K rho<1/4. Original norm(H0)<delta implies norm(A0(H0/2))<rho/2, hence the strict image and
Lipschitz bounds with q=3/4. The source analytic correction theorem constructs the genuine
correction. Original real ball persistence and continuity of A give one common nearby domain
where that ball is invariant, the original map is 3/4-Lipschitz and norm(A)<=norm(A0)+1.
Compare the actual fixed point with zero inside that original ball: its norm is at most
(3/4) times itself plus the actual half-forcing norm, hence at most four times that forcing.
The actual operator norm bound gives the displayed bound in terms of the original H norm.
Intersect this common open domain with the native analytic correction domain; all exact source
identities, original norm/equation/uniqueness, actual ball contraction and native analytic order
omega then hold on the same actual base set and original torus. No geometric T_F/metric defect,
source Q/Schauder construction or forcing smallness from geometry is silently supplied. -/
theorem collar_real_gram_small_forcing_analytic_correction {b a M N : ℕ}
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
      let K := ‖mult (AR p₀R)‖ * qNorm
      let ρ := 1 / (4 * (K + 1))
      let δ := ρ / (‖mult (AR p₀R)‖ + 1)
      0 < ρ ∧ 0 < δ ∧ (‖HR p₀R‖ < δ →
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
            ‖u p‖ ≤ 4 * ‖mult (AR (collarRealJointParameter b a (p, 0)))
              ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)))‖ ∧
            4 * ‖mult (AR (collarRealJointParameter b a (p, 0)))
              ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)))‖ ≤
                2 * (‖mult (AR p₀R)‖ + 1) * ‖HR (collarRealJointParameter b a (p, 0))‖ ∧
            ‖u p‖ ≤ 2 * (‖mult (AR p₀R)‖ + 1) *
              ‖HR (collarRealJointParameter b a (p, 0))‖ ∧
            mult (AR (collarRealJointParameter b a (p, 0)))
              ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q (u p) (u p)) = u p ∧
            ∀ v : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ), ‖v‖ ≤ ρ →
              (mult (AR (collarRealJointParameter b a (p, 0)))
                ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q v v) = v ↔ u p = v)) ∧
          (∀ p ∈ W,
            let S : Set (LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)) := {x | ‖x‖ ≤ ρ}
            let Φ := fun x ↦ mult (AR (collarRealJointParameter b a (p, 0)))
              ((1 / 2 : ℝ) • HR (collarRealJointParameter b a (p, 0)) + Q x x)
            MapsTo Φ S S ∧ LipschitzOnWith (3 / 4 : ℝ≥0) Φ S) ∧
          let _charted := periodicFlatTorusChartedSpace a
          ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin b))).prod
            (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ω
            (fun z : EuclideanSpace ℝ (Fin b) × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
              littlePeriodicCAlphaTorusValue (u z.1) z.2) (W ×ˢ univ)) := by
  dsimp only
  let p₀R := collarEuclideanRealEquiv (b + a)
    (toLp 2 (Fin.append p₀ (fun _ : Fin a ↦ (0 : ℝ))))
  let qNorm := ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
    (F := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ)) Q
  obtain ⟨V₀, hV₀, hpV₀, hsub, hright, AR, HR, mult, hAR, hHR, hsource, hmult, hbranch⟩ :=
    collar_real_gram_strict_base_analytic_correction T fH V hV p₀ hp₀ hT hfH
      hperiodT hperiodH hbase Q hQτ
  let A := fun p ↦ mult (AR p)
  let f := fun p ↦ mult (AR p) ((1 / 2 : ℝ) • HR p)
  let K := ‖A p₀R‖ * qNorm
  let ρ := 1 / (4 * (K + 1))
  let δ := ρ / (‖A p₀R‖ + 1)
  have hQN : 0 ≤ qNorm := by
    dsimp only [qNorm, ContinuousLinearMap.opNorm]
    exact Real.sInf_nonneg (fun c hc ↦ hc.1)
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg (A p₀R)) hQN
  have hdenom : 0 < 4 * (K + 1) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hK zero_lt_one)
  have hAnormpos : 0 < ‖A p₀R‖ + 1 :=
    add_pos_of_nonneg_of_pos (norm_nonneg (A p₀R)) zero_lt_one
  have hρ : 0 < ρ := one_div_pos.mpr hdenom
  have hδ : 0 < δ := div_pos hρ hAnormpos
  have hKr : K * ρ < (1 / 4 : ℝ) := by
    dsimp only [ρ]
    rw [mul_one_div, div_lt_iff₀ hdenom]
    nlinarith only []
  refine ⟨V₀, hV₀, hpV₀, hsub, hright, ?_⟩
  refine ⟨AR, HR, mult, ?_⟩
  refine ⟨hAR, hHR, hsource, hmult, ?_⟩
  change 0 < ρ ∧ 0 < δ ∧ _
  refine ⟨hρ, hδ, ?_⟩
  intro hsmall
  have hHt : ‖HR p₀R‖ * (‖A p₀R‖ + 1) < ρ :=
    (lt_div_iff₀ hAnormpos).mp hsmall
  have hfbound : ‖f p₀R‖ ≤ ‖A p₀R‖ * ((1 / 2 : ℝ) * ‖HR p₀R‖) := by
    calc
      ‖f p₀R‖ ≤ ‖A p₀R‖ * ‖(1 / 2 : ℝ) • HR p₀R‖ := (A p₀R).le_opNorm _
      _ = ‖A p₀R‖ * ((1 / 2 : ℝ) * ‖HR p₀R‖) := by rw [norm_smul]; norm_num
  have hfsmall : ‖f p₀R‖ < ρ / 2 := by
    nlinarith only [hHt, hfbound, norm_nonneg (HR p₀R)]
  have himage : ‖f p₀R‖ + ‖A p₀R‖ * qNorm * ρ ^ 2 < ρ := by
    have hs := mul_lt_mul_of_pos_right hKr hρ
    change ‖f p₀R‖ + K * ρ ^ 2 < ρ
    nlinarith only [hs, hfsmall, hρ]
  have hqval : ((3 / 4 : ℝ≥0) : ℝ) = (3 / 4 : ℝ) := by norm_num
  have hlip : 2 * ‖A p₀R‖ * qNorm * ρ < ((3 / 4 : ℝ≥0) : ℝ) := by
    rw [hqval]
    dsimp only [K] at hKr
    nlinarith only [hKr]
  obtain ⟨u, W, hWo, hpW, hpoint, hnative⟩ :=
    hbranch ρ hρ.le (3 / 4 : ℝ≥0) (by norm_num) himage hlip
  have hA : ContinuousAt A p₀R := mult.continuous.continuousAt.comp' hAR.continuousAt
  have hf : ContinuousAt f p₀R := hA.clm_apply (hHR.continuousAt.const_smul (1 / 2 : ℝ))
  have hpersist := collar_quadratic_ball_persistence
    (X := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
    (Y := LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ))
    A f Q p₀R hA hf ρ hρ.le (3 / 4 : ℝ≥0) himage hlip
  have hn : ContinuousAt (fun p ↦ ‖A p‖) p₀R := ContinuousAt.norm
    (E := LittlePeriodicCAlphaFunction a M 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)) (f := A) hA
  have hl : ∀ᶠ p in 𝓝 p₀R, ‖A p‖ < ‖A p₀R‖ + 1 :=
    hn.eventually_lt continuousAt_const (lt_add_one ‖A p₀R‖)
  have hAnorm : ∀ᶠ p in 𝓝 p₀R, ‖A p‖ ≤ ‖A p₀R‖ + 1 :=
    hl.mono (fun _ hp ↦ hp.le)
  have hc : Continuous (fun p : EuclideanSpace ℝ (Fin b) ↦
      collarRealJointParameter b a (p, 0)) :=
    (collarRealJointParameter b a).continuous.comp (continuous_id.prodMk continuous_const)
  have ht := hc.tendsto (toLp 2 p₀)
  rw [collar_real_joint_parameter_basepoint] at ht
  obtain ⟨B, hB, hBo, hpB⟩ := eventually_nhds_iff.mp (ht.eventually (hpersist.and hAnorm))
  refine ⟨u, W ∩ B, hWo.inter hBo, ⟨hpW, hpB⟩, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpV, hAp, hHp, hunorm, hufix, huunique⟩ := hpoint p hp.1
    let r := collarRealJointParameter b a (p, 0)
    have hfix : f r + A r (Q (u p) (u p)) = u p := by
      simpa only [A, f, map_add] using hufix
    have hzero : (0 : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ)) ∈
        {x | ‖x‖ ≤ ρ} := by simpa only [mem_ofPred_eq, norm_zero] using hρ.le
    have hd := (hB p hp.2).1.2.dist_le_mul (u p) hunorm 0 hzero
    change dist (f r + A r (Q (u p) (u p))) (f r + A r (Q 0 0)) ≤
      ((3 / 4 : ℝ≥0) : ℝ) * dist (u p) 0 at hd
    rw [hfix] at hd
    simp only [map_zero, add_zero, dist_zero_right] at hd
    rw [hqval] at hd
    have htri : ‖u p‖ ≤ dist (u p) (f r) + ‖f r‖ := by
      simpa only [dist_zero_right] using dist_triangle (u p) (f r) 0
    have hfour : ‖u p‖ ≤ 4 * ‖f r‖ := by linarith only [htri, hd]
    have hfsize : ‖f r‖ ≤ ‖A r‖ * ((1 / 2 : ℝ) * ‖HR r‖) := by
      calc
        ‖f r‖ ≤ ‖A r‖ * ‖(1 / 2 : ℝ) • HR r‖ := (A r).le_opNorm _
        _ = ‖A r‖ * ((1 / 2 : ℝ) * ‖HR r‖) := by rw [norm_smul]; norm_num
    have hcoeff := mul_le_mul_of_nonneg_right (hB p hp.2).2 (norm_nonneg (HR r))
    have hforcing : 4 * ‖f r‖ ≤ 2 * (‖A p₀R‖ + 1) * ‖HR r‖ := by
      nlinarith only [hfsize, hcoeff]
    have hlinear : ‖u p‖ ≤ 2 * (‖A p₀R‖ + 1) * ‖HR r‖ := hfour.trans hforcing
    exact ⟨hpV, hAp, hHp, hunorm, hfour, hforcing, hlinear, hufix, huunique⟩
  · intro p hp
    simpa only [A, f, map_add] using (hB p hp.2).1
  · dsimp only at hnative ⊢
    let _charted := periodicFlatTorusChartedSpace a
    exact hnative.mono (fun z hz ↦ ⟨hz.1.1, hz.2⟩)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_real_gram_small_forcing_analytic_correction
