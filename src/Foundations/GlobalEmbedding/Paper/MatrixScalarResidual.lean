import GlobalEmbedding.Paper.MatrixNativeAngleResidual
import GlobalEmbedding.Paper.MatrixScalarAnsatz
import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Actual oscillatory scalar residuals

Source: `main.tex`, `prop:matrix`, lines355–358.
DAG: `matrix-scalar-residual`.
The planar phase and all amplitudes are genuine fixed functions while the
scalar frequency varies. Oscillatory decay is reused from the actual Hopf theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

variable {C : ℕ} [Fact (0 < C)]

/-- The actual mean residual of η_b+r cos(Lt) tends uniformly to zero when the
already constructed actual base has mean zero.

Proof: split the actual continuous period integral. Its base part is exactly
zero, and its remaining part is the accepted actual fixed-amplitude Hopf
oscillatory average. Source: `prop:matrix`, lines355–358. -/
theorem matrix_scalar_linear_residual_tendsto_uniformly
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    (ηb r : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (hmean : ∀ z, orbitAverage planarHopfFlow ηb z = 0) :
    TendstoUniformly
      (fun L : ℝ ↦ orbitAverage planarHopfFlow
        (fun w ↦ ηb w + r w * Real.cos (L * matrixPlanarT f w)))
      (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
  have ht := (matrix_planar_data_contMDiff f hf).2.1
  have he (L : ℝ) (z : PlanarHopfSphere C) :
      orbitAverage planarHopfFlow
        (fun w ↦ ηb w + r w * Real.cos (L * matrixPlanarT f w)) z =
      orbitAverage planarHopfFlow (fun w ↦ r w * Real.cos (L * matrixPlanarT f w)) z := by
    have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
    have hi0 : IntervalIntegrable (fun t ↦ ηb (planarHopfFlow t z)) volume 0 1 :=
      (hb.continuous.comp hR).intervalIntegrable 0 1
    have hi1 : IntervalIntegrable
        (fun t ↦ r (planarHopfFlow t z) *
          Real.cos (L * matrixPlanarT f (planarHopfFlow t z))) volume 0 1 :=
      ((hr.continuous.comp hR).mul
        (Real.continuous_cos.comp (continuous_const.mul (ht.continuous.comp hR)))).intervalIntegrable 0 1
    change (∫ t in (0 : ℝ)..1,
      ηb (planarHopfFlow t z) + r (planarHopfFlow t z) *
        Real.cos (L * matrixPlanarT f (planarHopfFlow t z))) = _
    rw [intervalIntegral.integral_add hi0 hi1]
    change orbitAverage planarHopfFlow ηb z + _ = _
    rw [hmean z, zero_add]
    rfl
  have hc := matrix_hopf_uniform_oscillatory_average f hf hunit hana r hr 0
  simp only [add_zero] at hc
  convert hc using 1
  funext L z
  exact he L z

/-- Each actual quadratic moment residual tends uniformly to zero after the
actual density has canceled its constant part.

Proof: the exact cos(2x) identity expands a(η_b+r cos(Lt))² into
 a(η_b²+r²/2) + (2aη_b r)cos(Lt) + (ar²/2)cos(2Lt).
The first actual average is zero. The two remaining smooth fixed amplitudes
have actual uniform Hopf oscillatory decay at L and2L. Add their convergences.
Source: `prop:matrix`, lines355–358. -/
theorem matrix_scalar_quadratic_residual_tendsto_uniformly
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1)
    (hana : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) univ)
    (ηb r a : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (ha : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ a)
    (hmean : ∀ z, orbitAverage planarHopfFlow
      (fun w ↦ a w * (ηb w ^ 2 + r w ^ 2 / 2)) z = 0) :
    TendstoUniformly
      (fun L : ℝ ↦ orbitAverage planarHopfFlow
        (fun w ↦ a w * (ηb w + r w * Real.cos (L * matrixPlanarT f w)) ^ 2))
      (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
  let a0 : PlanarHopfSphere C → ℝ := fun w ↦ a w * (ηb w ^ 2 + r w ^ 2 / 2)
  let a1 : PlanarHopfSphere C → ℝ := fun w ↦ 2 * a w * ηb w * r w
  let a2 : PlanarHopfSphere C → ℝ := fun w ↦ a w * r w ^ 2 / 2
  have h0 : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ a0 :=
    ha.mul ((hb.pow 2).add ((hr.pow 2).div_const (c := (2 : ℝ))))
  have h1 : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ a1 :=
    ((contMDiff_const.mul ha).mul hb).mul hr
  have h2 : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ a2 :=
    (ha.mul (hr.pow 2)).div_const (c := (2 : ℝ))
  have ht := (matrix_planar_data_contMDiff f hf).2.1
  have he (L : ℝ) (z : PlanarHopfSphere C) :
      orbitAverage planarHopfFlow
        (fun w ↦ a w * (ηb w + r w * Real.cos (L * matrixPlanarT f w)) ^ 2) z =
      orbitAverage planarHopfFlow (fun w ↦ a1 w * Real.cos (L * matrixPlanarT f w)) z +
        orbitAverage planarHopfFlow (fun w ↦ a2 w * Real.cos ((2 * L) * matrixPlanarT f w)) z := by
    have heq : (fun w ↦ a w * (ηb w + r w * Real.cos (L * matrixPlanarT f w)) ^ 2) =
        (fun w ↦ (a0 w + a1 w * Real.cos (L * matrixPlanarT f w)) +
          a2 w * Real.cos ((2 * L) * matrixPlanarT f w)) := by
      funext w
      rw [show (2 * L) * matrixPlanarT f w = 2 * (L * matrixPlanarT f w) by ring,
        Real.cos_two_mul]
      dsimp [a0, a1, a2]
      ring
    rw [heq]
    have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
    have hi0 : IntervalIntegrable (fun t ↦ a0 (planarHopfFlow t z)) volume 0 1 :=
      (h0.continuous.comp hR).intervalIntegrable 0 1
    have hi1 : IntervalIntegrable
        (fun t ↦ a1 (planarHopfFlow t z) *
          Real.cos (L * matrixPlanarT f (planarHopfFlow t z))) volume 0 1 :=
      ((h1.continuous.comp hR).mul
        (Real.continuous_cos.comp (continuous_const.mul (ht.continuous.comp hR)))).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable
        (fun t ↦ a2 (planarHopfFlow t z) *
          Real.cos ((2 * L) * matrixPlanarT f (planarHopfFlow t z))) volume 0 1 :=
      ((h2.continuous.comp hR).mul
        (Real.continuous_cos.comp (continuous_const.mul (ht.continuous.comp hR)))).intervalIntegrable 0 1
    unfold orbitAverage
    rw [intervalIntegral.integral_add (hi0.add hi1) hi2, intervalIntegral.integral_add hi0 hi1]
    change (orbitAverage planarHopfFlow a0 z + _) + _ = _
    rw [show orbitAverage planarHopfFlow a0 z = 0 from hmean z, zero_add]
  have hc1 := matrix_hopf_uniform_oscillatory_average f hf hunit hana a1 h1 0
  have hc2 : TendstoUniformly
      (fun L : ℝ ↦ orbitAverage planarHopfFlow
        (fun w ↦ a2 w * Real.cos ((2 * L) * matrixPlanarT f w + 0)))
      (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
    intro V hV
    exact (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      ((matrix_hopf_uniform_oscillatory_average f hf hunit hana a2 h2 0) V hV)
  have hc := hc1.add hc2
  simp only [add_zero] at hc
  convert hc using 1
  · funext L z
    exact he L z
  · funext z
    simp only [Pi.add_apply, zero_add]

/-- The complete actual finite-dimensional scalar residual tends uniformly to
zero in its genuine Euclidean coefficient norm, using the same actual planar f.

Proof: each scalar coordinate is one of the two actual residuals just proved.
Continuous coordinate projections commute with the integrable actual period
integral. Uniform convergence to zero is convergence along atTop times the top
base filter; finite coordinate convergence and the actual Euclidean equivalence
therefore give convergence in the actual l² norm.
Source: `prop:matrix`, lines355–358. -/
theorem matrix_scalar_residual_tendsto_uniformly
    {m : ℕ} (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (κ ηb r : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (hmean : ∀ z, orbitAverage planarHopfFlow ηb z = 0)
    (hquad : ∀ i z, orbitAverage planarHopfFlow
      (fun w ↦ A w i * (ηb w ^ 2 + r w ^ 2 / 2)) z = 0) :
    TendstoUniformly
      (fun L : ℝ ↦ fun z ↦ matrixScalarMomentMap A κ
        (matrixScalarOscillatoryBase f ηb r L) z 0)
      (fun _ : PlanarHopfSphere C ↦ (0 : MatrixScalarCoefficients m)) atTop := by
  have ht := (matrix_planar_data_contMDiff f hf.smooth).2.1
  have hentry (L : ℝ) (z : PlanarHopfSphere C) (i : Option (Fin m)) :
      matrixScalarMomentMap A κ (matrixScalarOscillatoryBase f ηb r L) z 0 i =
      match i with
      | none => orbitAverage planarHopfFlow
          (fun w ↦ ηb w + r w * Real.cos (L * matrixPlanarT f w)) z
      | some j => orbitAverage planarHopfFlow
          (fun w ↦ A w j * (ηb w + r w * Real.cos (L * matrixPlanarT f w)) ^ 2) z := by
    let u := matrixScalarOscillatoryBase f ηb r L
    have hu : Continuous u := hb.continuous.add (hr.continuous.mul
      (Real.continuous_cos.comp (continuous_const.mul ht.continuous)))
    have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      ((planarHopfFlow_contMDiff C).comp (contMDiff_id.prodMk contMDiff_const)).continuous
    have hv : Continuous (fun w ↦ matrixScalarMomentValues A (u w) w) := by
      apply (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.continuous.comp
      apply continuous_pi
      intro j
      cases j with
      | none => exact hu
      | some j =>
        exact (hu.pow 2).mul
          ((EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin m) j).continuous.comp hA.continuous)
    have hi : IntervalIntegrable
        (fun t ↦ matrixScalarMomentValues A (u (planarHopfFlow t z)) (planarHopfFlow t z))
        volume 0 1 := (hv.comp hR).intervalIntegrable 0 1
    change (∫ t in (0 : ℝ)..1, matrixScalarMomentValues A
      (matrixScalarAnsatz A κ u 0 (planarHopfFlow t z)) (planarHopfFlow t z)) i = _
    simp only [matrixScalarAnsatz_zero]
    change (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i)
      (∫ t in (0 : ℝ)..1,
        matrixScalarMomentValues A (u (planarHopfFlow t z)) (planarHopfFlow t z)) = _
    rw [← (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Option (Fin m)) i).intervalIntegral_comp_comm hi]
    cases i with
    | none => rfl
    | some j =>
      unfold orbitAverage
      apply intervalIntegral.integral_congr
      intro t _
      change u (planarHopfFlow t z) ^ 2 * A (planarHopfFlow t z) j =
        A (planarHopfFlow t z) j * u (planarHopfFlow t z) ^ 2
      exact mul_comm _ _
  have hcoord (i : Option (Fin m)) : TendstoUniformly
      (fun L : ℝ ↦ fun z ↦
        matrixScalarMomentMap A κ (matrixScalarOscillatoryBase f ηb r L) z 0 i)
      (fun _ : PlanarHopfSphere C ↦ (0 : ℝ)) atTop := by
    cases i with
    | none =>
      have h := matrix_scalar_linear_residual_tendsto_uniformly
        f hf.smooth hf.unit_speed hf.orbit_analytic ηb r hb hr hmean
      convert h using 1
      funext L z
      exact hentry L z none
    | some j =>
      have ha := (EuclideanSpace.proj (𝕜 := ℝ) («ι» := Fin m) j).contMDiff.comp hA
      have h := matrix_scalar_quadratic_residual_tendsto_uniformly
        f hf.smooth hf.unit_speed hf.orbit_analytic ηb r (fun w ↦ A w j) hb hr ha (hquad j)
      convert h using 1
      funext L z
      exact hentry L z (some j)
  apply tendsto_prod_top_iff.mp
  have hpi : Tendsto
      (fun p : ℝ × PlanarHopfSphere C ↦ fun i : Option (Fin m) ↦
        matrixScalarMomentMap A κ (matrixScalarOscillatoryBase f ηb r p.1) p.2 0 i)
      (atTop ×ˢ ⊤) (𝓝 (0 : Option (Fin m) → ℝ)) :=
    tendsto_pi_nhds.mpr (fun i ↦ tendsto_prod_top_iff.mpr (hcoord i))
  exact (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.continuous.continuousAt.tendsto.comp hpi

#print axioms matrix_scalar_linear_residual_tendsto_uniformly
#print axioms matrix_scalar_quadratic_residual_tendsto_uniformly
#print axioms matrix_scalar_residual_tendsto_uniformly

end GlobalEmbedding.Paper
