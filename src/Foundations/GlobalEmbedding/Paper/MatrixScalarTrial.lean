import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import GlobalEmbedding.Paper.MatrixScalarBase
import GlobalEmbedding.Paper.MatrixPositiveMomentDensity

/-!
# Actual fixed scalar trial amplitudes

Source: `main.tex`, `prop:matrix`, lines355–357.
DAG: `matrix-scalar-trial`.
Both eta_b and r=sqrt(2rho) are genuinely constructed from the same actual
planar selector and the actual positive orbit cone; neither is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- Construct the actual base and oscillatory amplitude, with all actual smooth,
flat, positive and constant-moment properties needed by the scalar correction.

Proof: construct the literal eta_b using the accepted zero-mean base theorem.
Set y=-av(eta_b² A); actual compact integration makes y smooth and basic.
Apply the accepted genuine positive-density theorem to this y and put
r=sqrt(2rho). Its full flatness and strict positivity off zero curvature are
genuine outputs. The square identity r²=2rho and real period-integral linearity
cancel the constant vector moment exactly. Actual coordinate continuous linear
maps commute with that integrable vector period, giving each scalar coordinate
identity. Source: `prop:matrix`, lines355–357. -/
theorem matrix_scalar_trial_exists {C m : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (hspan : ∀ z, ∀ v : EuclideanSpace ℝ (Fin m), v ≠ 0 → ∃ t : ℝ,
      planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) ≠ 0 ∧
        0 < ⟪A (planarHopfFlow t z), v⟫) :
    ∃ ηb r : PlanarHopfSphere C → ℝ,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb ∧
      (∀ z, orbitAverage planarHopfFlow ηb z = 0) ∧
      ManifoldFlatOn (I := planarHopfModel C)
        (fun z ↦ ηb z - ‖f z‖ ^ 2 / 2) {z | planarOrbitCurvature planarHopfFlow f z = 0} ∧
      ManifoldFlatOn (I := planarHopfModel C) r {z | planarOrbitCurvature planarHopfFlow f z = 0} ∧
      (∀ z, planarOrbitCurvature planarHopfFlow f z ≠ 0 → 0 < r z) ∧
      (∀ z, orbitAverage planarHopfFlow
        (fun w ↦ (ηb w ^ 2 + r w ^ 2 / 2) • A w) z = 0) ∧
      (∀ i z, orbitAverage planarHopfFlow
        (fun w ↦ A w i * (ηb w ^ 2 + r w ^ 2 / 2)) z = 0) := by
  let κ := planarOrbitCurvature planarHopfFlow f
  have hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ := hf.curvature_smooth
  have hn (z : PlanarHopfSphere C) : ∃ t : ℝ, κ (planarHopfFlow t z) ≠ 0 := by
    obtain ⟨t, s, ht, _⟩ := hf.curvature_signs z
    exact ⟨t, ht.ne⟩
  let ηb := matrixScalarBase f κ
  obtain ⟨hb, hbmean, hbflat⟩ := matrixScalarBase_properties f κ hf.smooth hκ hn
  let g : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m) := fun w ↦ ηb w ^ 2 • A w
  have hg : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ g :=
    (hb.pow 2).smul hA
  let y := fun z ↦ -orbitAverage planarHopfFlow g z
  have hy : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ y :=
    (planarHopfAverage_contMDiff g hg).neg
  have hybasic (t : ℝ) (z : PlanarHopfSphere C) : y (planarHopfFlow t z) = y z := by
    simp only [y, planarHopfAverage_flow]
  obtain ⟨ρ, hρflat, hρnonneg, hρpos, hrflat, hρmean⟩ :=
    matrix_positive_moment_density_sqrt_two κ A y hκ hA hy hybasic hspan
  let r : PlanarHopfSphere C → ℝ := fun z ↦ Real.sqrt (2 * ρ z)
  have hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r := hrflat.1
  have hrsq (z : PlanarHopfSphere C) : r z ^ 2 / 2 = ρ z := by
    dsimp [r]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) (hρnonneg z))]
    ring
  have hp (z : PlanarHopfSphere C) (hz : κ z ≠ 0) : 0 < r z :=
    Real.sqrt_pos.mpr (mul_pos (by norm_num) (hρpos z hz))
  have havg (z : PlanarHopfSphere C) : orbitAverage planarHopfFlow
      (fun w ↦ (ηb w ^ 2 + r w ^ 2 / 2) • A w) z = 0 := by
    have he : (fun w ↦ (ηb w ^ 2 + r w ^ 2 / 2) • A w) =
        (fun w ↦ g w + ρ w • A w) := by
      funext w
      rw [hrsq, add_smul]
    rw [he]
    have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
    have hi0 : IntervalIntegrable (fun t ↦ g (planarHopfFlow t z)) volume 0 1 :=
      (hg.continuous.comp hR).intervalIntegrable 0 1
    have hi1 : IntervalIntegrable
        (fun t ↦ ρ (planarHopfFlow t z) • A (planarHopfFlow t z)) volume 0 1 :=
      ((hρflat.1.smul hA).continuous.comp hR).intervalIntegrable 0 1
    unfold orbitAverage
    rw [intervalIntegral.integral_add hi0 hi1]
    change orbitAverage planarHopfFlow g z +
      orbitAverage planarHopfFlow (fun w ↦ ρ w • A w) z = 0
    rw [hρmean z]
    exact add_neg_cancel _
  refine ⟨ηb, r, hb, hbmean, hbflat, hrflat, hp, havg, ?_⟩
  intro i z
  have hF : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun w ↦ (ηb w ^ 2 + r w ^ 2 / 2) • A w) :=
    ((hb.pow 2).add ((hr.pow 2).div_const (c := (2 : ℝ)))).smul hA
  have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
    ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
  have hi : IntervalIntegrable
      (fun t ↦ (ηb (planarHopfFlow t z) ^ 2 + r (planarHopfFlow t z) ^ 2 / 2) •
        A (planarHopfFlow t z)) volume 0 1 :=
    (hF.continuous.comp hR).intervalIntegrable 0 1
  have he := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin m) i).intervalIntegral_comp_comm hi
  calc
    _ = (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin m) i)
        (orbitAverage planarHopfFlow
          (fun w ↦ (ηb w ^ 2 + r w ^ 2 / 2) • A w) z) := by
      unfold orbitAverage
      rw [← he]
      apply intervalIntegral.integral_congr
      intro t _
      change A (planarHopfFlow t z) i *
        (ηb (planarHopfFlow t z) ^ 2 + r (planarHopfFlow t z) ^ 2 / 2) =
        (ηb (planarHopfFlow t z) ^ 2 + r (planarHopfFlow t z) ^ 2 / 2) * A (planarHopfFlow t z) i
      exact mul_comm _ _
    _ = 0 := by rw [havg z]; rfl

#print axioms matrix_scalar_trial_exists

end GlobalEmbedding.Paper
