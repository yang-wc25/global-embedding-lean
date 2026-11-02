import GlobalEmbedding.Paper.MatrixScalarHessian
import GlobalEmbedding.Paper.MatrixScalarResidual
import GlobalEmbedding.Paper.MatrixManifoldHessianCorrection

/-!
# A genuine smooth basic correction of the actual scalar moments

Source: `main.tex`, `prop:matrix`, lines355–365.
DAG: `matrix-scalar-small-correction`.
All analytic inputs except the actual Gram inverse are already discharged by
the original fixed scalar equations, rather than assumed abstract estimates.
-/

noncomputable section
open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Fix one sufficiently large real scalar frequency and construct true smooth
basic coefficients solving the actual original scalar moment equation.

Proof: the actual Jacobian is the original scalar Gram. Its supplied actual
inverse estimate is the separately proved scalar-Gram branch, with no solver
assumption. The actual scalar equations are jointly native smooth, their real
residual tends uniformly to zero, and their actual Hessians have one bound for
all frequencies and coefficients. Choose radius 1/(4D(K+1)) and residual
radius/(4D), then choose a frequency meeting the actual inverse and residual
thresholds. Apply the already proved native Hessian correction theorem to this
literal H at that fixed frequency. Its uniqueness and the proved actual orbit
invariance of H give basicness of the actual selected coefficient field.
Source: `prop:matrix`, lines355–365. -/
theorem matrix_scalar_small_correction {C m : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (ηb r : PlanarHopfSphere C → ℝ)
    (hb : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ ηb)
    (hr : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ r)
    (hmean : ∀ z, orbitAverage planarHopfFlow ηb z = 0)
    (hquad : ∀ i z, orbitAverage planarHopfFlow
      (fun w ↦ A w i * (ηb w ^ 2 + r w ^ 2 / 2)) z = 0)
    (hinverse : ∃ Mbound : ℝ, 0 < Mbound ∧ ∀ᶠ L : ℝ in atTop, ∀ z : PlanarHopfSphere C,
      ∃ e : MatrixScalarCoefficients m ≃L[ℝ] MatrixScalarCoefficients m,
        e.toContinuousLinearMap = matrixScalarGram A (planarOrbitCurvature planarHopfFlow f)
          (matrixScalarOscillatoryBase f ηb r L) z ∧ ‖e.symm.toContinuousLinearMap‖ ≤ Mbound) :
    ∃ L : ℝ, ∃ c : PlanarHopfSphere C → MatrixScalarCoefficients m,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixScalarCoefficients m) ∞ c ∧
      (∀ s z, c (planarHopfFlow s z) = c z) ∧
      ∀ z, matrixScalarMomentMap A (planarOrbitCurvature planarHopfFlow f)
        (matrixScalarOscillatoryBase f ηb r L) z (c z) = 0 := by
  classical
  let κ := planarOrbitCurvature planarHopfFlow f
  have hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ := hf.curvature_smooth
  obtain ⟨Mbound, hD, hinv⟩ := hinverse
  obtain ⟨K, hK, hHess⟩ := matrixScalarMomentMap_uniform_hessian_bound
    f hf.smooth A κ ηb r hA.continuous hκ.continuous hb.continuous hr.continuous
  let radius : ℝ := (4 * Mbound * (K + 1))⁻¹
  have hden : 0 < 4 * Mbound * (K + 1) := by positivity
  have hrad : 0 < radius := inv_pos.mpr hden
  have hprod : 4 * Mbound * (K + 1) * radius = 1 := mul_inv_cancel₀ hden.ne'
  have hsmall : 4 * Mbound * K * radius ≤ 1 := by
    have hp : 0 ≤ 4 * Mbound * radius := by positivity
    nlinarith [hprod]
  let ε : ℝ := radius / (4 * Mbound)
  have hε : 0 < ε := div_pos hrad (by positivity)
  have heq : Mbound * ε = radius / 4 := by
    dsimp [ε]
    field_simp [hD.ne']
  have hresSmall : Mbound * ε ≤ radius / 2 := by rw [heq]; linarith
  have hdecay := matrix_scalar_residual_tendsto_uniformly f hf A hA κ ηb r hb hr hmean hquad
  have hres := (Metric.tendstoUniformly_iff.mp hdecay) ε hε
  obtain ⟨L, hLi, hLres⟩ := (hinv.and hres).exists
  let u := matrixScalarOscillatoryBase f ηb r L
  have ht := (matrix_planar_data_contMDiff f hf.smooth).2.1
  have hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u :=
    hb.add (hr.mul (Real.contDiff_cos.contMDiff.comp (contMDiff_const.mul ht)))
  let E : PlanarHopfSphere C → MatrixScalarCoefficients m ≃L[ℝ] MatrixScalarCoefficients m :=
    fun z ↦ (hLi z).choose
  have he (z : PlanarHopfSphere C) :
      (E z).toContinuousLinearMap = matrixScalarGram A κ u z ∧
        ‖(E z).symm.toContinuousLinearMap‖ ≤ Mbound := (hLi z).choose_spec
  obtain ⟨c, hc, hroot, heqroot⟩ := manifold_hessian_small_residual_correction
    (matrixScalarMomentMap A κ u) E radius Mbound K ε hrad hD hK hε.le hsmall hresSmall
    (matrixScalarMomentMap_contMDiff A hA κ u hκ hu)
    (fun z ↦ (he z).1.trans
      (matrixScalarMomentMap_fderiv_zero A κ u hA.continuous hκ.continuous hu.continuous z).symm)
    (fun z ↦ (he z).2)
    (fun z a _ ↦ hHess L z a)
    (fun z ↦ by simpa only [dist_zero_left, norm_neg] using (hLres z).le)
  refine ⟨L, c, hc, ?_, fun z ↦ (hroot z).1⟩
  intro s z
  exact heqroot (planarHopfFlow s z) z
    (fun a ↦ matrixScalarMomentMap_flow A κ u z s a)

#print axioms matrix_scalar_small_correction

end GlobalEmbedding.Paper
