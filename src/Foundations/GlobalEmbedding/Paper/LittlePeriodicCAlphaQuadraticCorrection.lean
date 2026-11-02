import GlobalEmbedding.Paper.LittlePeriodicCAlphaNativeJointSmooth
import GlobalEmbedding.Paper.PeriodicCAlphaGlobalJetBound
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The actual rescaled correction has uniform quadratic vertical jet bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 403–425.
DAG node: `balanced-holder-quadratic-correction-rescaling`.
-/

open Set
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Actual rescaling gives a smooth quadratic-size correction with every original vertical jet.

Set u(p,t)=t times the original little-space branch. Genuine scalar multiplication preserves
norm smoothness, and actual translation linearity gives smoothness of the translated orbit.
Native descent gives true joint parameter/time/torus smoothness. Norm homogeneity turns the
original linear bound into C t², and the actual global jet bound controls every original
lift derivative through order k at every point. At t=0 the size bound makes v=0; the genuine
product derivative therefore makes the entire first differential of u vanish there.
Source: U=epsilon v and the vertical C² estimate in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_quadratic_correction_rescaling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a N k : ℕ} {α : ℝ}
    (V : Set E) (hV : IsOpen V) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (v : E × ℝ → LittlePeriodicCAlphaFunction a N k α)
    (hv : ContDiffOn ℝ ∞ v (V ×ˢ Metric.ball (0 : ℝ) δ))
    (horbit : ContDiffOn ℝ ∞ (fun z : (E × ℝ) × EuclideanSpace ℝ (Fin a) ↦
      littlePeriodicCAlphaTranslateIsometry z.2 (v z.1))
      ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ))
    (hsize : ∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ, ‖v z‖ ≤ C * |z.2|) :
    let u := fun z : E × ℝ ↦ z.2 • v z
    ContDiffOn ℝ ∞ u (V ×ˢ Metric.ball (0 : ℝ) δ) ∧
      (∀ p : E, u (p, 0) = 0) ∧
      (∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ,
        ‖u z‖ ≤ C * z.2 ^ 2 ∧
          ∀ j ≤ k, ∀ x : EuclideanSpace ℝ (Fin a),
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
  dsimp only
  let u := fun z : E × ℝ ↦ z.2 • v z
  have hu : ContDiffOn ℝ ∞ u (V ×ˢ Metric.ball (0 : ℝ) δ) :=
    contDiff_snd.contDiffOn.smul hv
  have huorbit : ContDiffOn ℝ ∞ (fun z : (E × ℝ) × EuclideanSpace ℝ (Fin a) ↦
      littlePeriodicCAlphaTranslateIsometry z.2 (u z.1))
      ((V ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ univ) := by
    apply (((contDiff_snd.comp contDiff_fst).contDiffOn).smul horbit).congr
    intro z hz
    exact map_smul (littlePeriodicCAlphaTranslateIsometry z.2) z.1.2 (v z.1)
  refine ⟨hu, fun p ↦ zero_smul ℝ _, ?_, ?_, huorbit, ?_⟩
  · intro z hz
    have hnorm : ‖u z‖ ≤ C * z.2 ^ 2 := by
      calc
        ‖u z‖ = |z.2| * ‖v z‖ := by
          change ‖z.2 • v z‖ = _
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |z.2| * (C * |z.2|) :=
          mul_le_mul_of_nonneg_left (hsize z hz) (abs_nonneg z.2)
        _ = C * |z.2| ^ 2 := by ring
        _ = C * z.2 ^ 2 := by rw [sq_abs]
    refine ⟨hnorm, fun j hj x ↦ ?_⟩
    exact (periodicCAlpha_global_jet_bound (u z).val j hj x).trans hnorm
  · intro p hp
    have hp0 : (p, (0 : ℝ)) ∈ V ×ˢ Metric.ball (0 : ℝ) δ :=
      ⟨hp, by simpa using hδ⟩
    have hzero : v (p, 0) = 0 := by
      have h := hsize (p, 0) hp0
      simp only [abs_zero, mul_zero] at h
      exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    have hdiff := (hv.contDiffAt ((hV.prod Metric.isOpen_ball).mem_nhds hp0)).differentiableAt
      (by norm_num)
    convert (hasFDerivAt_snd (𝕜 := ℝ) (p := (p, (0 : ℝ)))).smul hdiff.hasFDerivAt
      using 1
    simp [hzero]
  · exact littlePeriodicCAlpha_native_joint_smooth_of_orbit
      (V ×ˢ Metric.ball (0 : ℝ) δ) (hV.prod Metric.isOpen_ball) u huorbit

#print axioms littlePeriodicCAlpha_quadratic_correction_rescaling

end GlobalEmbedding.Paper
