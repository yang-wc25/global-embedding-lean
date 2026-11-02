import GlobalEmbedding.Paper.BalancedFixedTranslatedSourceData
import GlobalEmbedding.Paper.BalancedCompactNeighborhoodSmoothBranch
import GlobalEmbedding.Paper.LittlePeriodicCAlphaEquivariantFixedSmooth
import GlobalEmbedding.Paper.LittlePeriodicCAlphaQuadraticCorrection

/-!
# Actual compact-source small branches and quadratic native corrections

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 365–425.
DAG node: `balanced-holder-compact-source-correction`.
-/

open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Original source data near a compact parameter set construct an actual smooth small correction.

The original source theorem proves actual norm-smooth data and genuine translated-data
smoothness, without assuming either. Original forcing vanishes at zero on the entire
original open base domain. The compact-neighborhood branch theorem constructs a genuine
open neighborhood of the whole compact set and one common time interval, deriving all
uniform bounds from compactness. The equivariant implicit theorem and genuine torus descent
give actual joint fiber smoothness. Actual rescaling by time gives the correction, its
original pointwise vertical jet bounds C t² and zero first differential at time zero.
No selected solution, prior uniform bound or native smoothness is assumed. The paper's
actual bounded symmetric equivariant Q remains an explicit separate construction premise.
Source: the local analytic common-interval correction argument in `lem:balanced`. -/
theorem littlePeriodicCAlpha_compact_source_correction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a M N : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a M 2 α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) (hR : 0 < R)
    (A : E × ℝ → LittlePeriodicCAlphaFunction a M 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (f : E × ℝ → LittlePeriodicCAlphaFunction a N 2 α)
    (sourceA : E × ℝ → EuclideanSpace ℝ (Fin a) →
      (EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    (sourcef : E × ℝ → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hsA : ContDiffOn ℝ ∞ (Function.uncurry sourceA)
      ((U ×ˢ Metric.ball (0 : ℝ) R) ×ˢ univ))
    (hsf : ContDiffOn ℝ ∞ (Function.uncurry sourcef)
      ((U ×ˢ Metric.ball (0 : ℝ) R) ×ˢ univ))
    (hperiodA : ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) R,
      ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
        sourceA z (x + toLp 2 (fun i ↦ (m i : ℝ))) = sourceA z x)
    (hperiodf : ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) R,
      ∀ (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
        sourcef z (x + toLp 2 (fun i ↦ (m i : ℝ))) = sourcef z x)
    (hAvalue : ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) R,
      ∀ (u : LittlePeriodicCAlphaFunction a M 2 α) x,
        (A z u).val.toFun x = sourceA z x (u.val.toFun x))
    (hfvalue : ∀ z ∈ U ×ˢ Metric.ball (0 : ℝ) R, ∀ x,
      (f z).val.toFun x = sourcef z x)
    (hsourcef0 : ∀ p ∈ U, ∀ x, sourcef (p, 0) x = 0)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) ∧
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ δ < R ∧
      ∃ v : E × ℝ → LittlePeriodicCAlphaFunction a N 2 α,
        ContDiffOn ℝ ∞ v (V ×ˢ Metric.ball (0 : ℝ) δ) ∧
        (∀ p ∈ V, v (p, 0) = 0) ∧
        (∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ,
          v z = f z + A z (Q (v z) (v z)) ∧ ‖v z‖ ≤ C * |z.2| ∧
            ‖(2 : ℝ) • (A z).comp (Q (v z))‖ ≤ 1 / 2 ∧
            (ContinuousLinearMap.id ℝ _ - (2 : ℝ) • (A z).comp (Q (v z))).IsInvertible ∧
            ‖(ContinuousLinearMap.id ℝ _ - (2 : ℝ) • (A z).comp (Q (v z))).inverse‖ ≤ 2) ∧
        (∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ,
          ∀ w : LittlePeriodicCAlphaFunction a N 2 α,
            w = f z + A z (Q w w) → ‖(2 : ℝ) • (A z).comp (Q w)‖ < 1 → w = v z) ∧
        ContDiffOn ℝ ∞ (fun z : (E × ℝ) × EuclideanSpace ℝ (Fin a) ↦
          littlePeriodicCAlphaTranslateIsometry z.2 (v z.1))
          ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ) ∧
        ContDiffOn ℝ ∞ (fun z : (E × ℝ) × EuclideanSpace ℝ (Fin a) ↦
          (v z.1).val.toFun z.2) ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ) ∧
        (let _charted := periodicFlatTorusChartedSpace a;
          ContMDiffOn ((𝓘(ℝ, E × ℝ)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin a))))
            (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ∞
            (fun z : (E × ℝ) × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
              littlePeriodicCAlphaTorusValue (v z.1) z.2)
            ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ)) ∧
    let u := fun z : E × ℝ ↦ z.2 • v z
    ContDiffOn ℝ ∞ u (V ×ˢ Metric.ball (0 : ℝ) δ) ∧
      (∀ p : E, u (p, 0) = 0) ∧
      (∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ,
        ‖u z‖ ≤ C * z.2 ^ 2 ∧
          ∀ j ≤ 2, ∀ x : EuclideanSpace ℝ (Fin a),
            ‖iteratedFDeriv ℝ j (u z).val.toFun x‖ ≤ C * z.2 ^ 2) ∧
      (∀ p ∈ V, HasFDerivAt (𝕜 := ℝ) u 0 (p, 0)) ∧
      ContDiffOn ℝ ∞ (fun z : (E × ℝ) × EuclideanSpace ℝ (Fin a) ↦
        littlePeriodicCAlphaTranslateIsometry z.2 (u z.1))
        ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ) ∧
      (let _charted := periodicFlatTorusChartedSpace a;
        ContMDiffOn ((𝓘(ℝ, E × ℝ)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin a))))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ∞
          (fun z : (E × ℝ) × PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
            littlePeriodicCAlphaTorusValue (u z.1) z.2)
          ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ)) := by
  obtain ⟨hf, hA, hfτ, hAτ⟩ := balanced_fixed_translated_source_data
    (U ×ˢ Metric.ball (0 : ℝ) R) (hU.prod Metric.isOpen_ball) A f sourceA sourcef
    hsA hsf hperiodA hperiodf hAvalue hfvalue hα0 hα1
  have hf0 : ∀ p ∈ U, f (p, 0) = 0 := by
    intro p hp
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    change (f (p, 0)).val.toFun = (0 : PeriodicCAlphaFunction a N 2 α).toFun
    rw [(periodicCAlpha_pointwise_operations a N 2 α).1]
    funext x
    exact (hfvalue (p, 0) ⟨hp, by simpa using hR⟩ x).trans (hsourcef0 p hp x)
  obtain ⟨V, hV, hKV, hclU, hclcomp, δ, C, hδ, hC, hδR, v, hv, hv0, hspec, huniq⟩ :=
    balanced_compact_neighborhood_smooth_branch Q hQsym U K hU hK hKU R hR A f hf hA hf0
  have hsub : V ×ˢ Metric.ball (0 : ℝ) δ ⊆ U ×ˢ Metric.ball (0 : ℝ) R := by
    intro z hz
    exact ⟨hclU (subset_closure hz.1), Metric.ball_subset_ball hδR.le hz.2⟩
  have hsubτ : (V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ
      (univ : Set (EuclideanSpace ℝ (Fin a))) ⊆
      (U ×ˢ Metric.ball (0 : ℝ) R) ×ˢ univ := fun z hz ↦ ⟨hsub hz.1, hz.2⟩
  have heq := littlePeriodicCAlpha_equivariant_fixed_joint_smooth
    (V ×ˢ Metric.ball (0 : ℝ) δ) (hV.prod Metric.isOpen_ball) Q hQsym hQτ f A v
    (hfτ.mono hsubτ) (hAτ.mono hsubτ) (fun z hz ↦ (hspec z hz).1)
    (fun z hz ↦ (hspec z hz).2.2.1.trans_lt (by norm_num))
  have hnative := littlePeriodicCAlpha_native_joint_smooth_of_orbit
    (V ×ˢ Metric.ball (0 : ℝ) δ) (hV.prod Metric.isOpen_ball) v heq.1
  have hcorrection := littlePeriodicCAlpha_quadratic_correction_rescaling V hV δ hδ C v hv
    heq.1 (fun z hz ↦ (hspec z hz).2.1)
  exact ⟨V, hV, hKV, hclU, hclcomp, δ, C, hδ, hC, hδR, v, hv, hv0, hspec, huniq,
    heq.1, heq.2, hnative, hcorrection⟩

#print axioms littlePeriodicCAlpha_compact_source_correction

end GlobalEmbedding.Paper
