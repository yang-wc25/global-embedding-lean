import GlobalEmbedding.Paper.MatrixScalarTrial
import GlobalEmbedding.Paper.MatrixScalarGramLimit
import GlobalEmbedding.Paper.MatrixScalarCorrection
import GlobalEmbedding.Paper.MatrixScalarMomentInterpretation
import GlobalEmbedding.Paper.ManifoldFlatOnAdd

/-!
# The actual scalar moment construction

Source: `main.tex`, `prop:matrix`, lines355–365.
DAG: `matrix-scalar-moment`.
The same actual planar selector and actual positive orbit cone construct eta.
No desired density, trial, inverse, coefficient field or scalar solution is assumed.
-/

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- The actual positive orbit cone constructs a smooth scalar eta with both exact
original scalar moments, whose difference from |f|²/2 is fully natively flat.

Proof: use the actual scalar trial theorem to construct eta_b and the literal
r=sqrt(2rho), with the actual zero mean, constant quadratic-moment cancellation,
full native flatness, and positivity away from curvature zero. The actual scalar
Gram theorem gives one eventual uniform inverse bound from the actual orbit
cone. Actual oscillatory residual decay, the true Jacobian identity, true
native smoothness and the actual uniform coefficient Hessian discharge every
other hypothesis of the accepted Hessian small-root theorem. Its actual
application fixes one sufficiently large real frequency and selects a native
smooth basic coefficient field solving the original finite-dimensional moment
equations. Define eta by the literal cutoff-weighted scalar ansatz evaluated
at those coefficients. Basicness identifies its actual orbit moments with the
solved fixed-coefficient moments; continuous coordinate maps commute with
actual integrable period integrals. All corrections are fully flat in every
native smooth chart: the base difference is flat, r times cosine is flat, and
the selected coefficient correction is a genuine cutoff smooth multiple. The
actual all-chart jet addition theorem sums these differences to give exactly
eta−|f|²/2 flat on the actual zero-curvature set. This works in every finite
moment dimension, including zero.
Source: `prop:matrix`, lines355–365. -/
theorem matrix_scalar_moment {C m : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ A)
    (hspan : ∀ z, ∀ v : EuclideanSpace ℝ (Fin m), v ≠ 0 → ∃ t : ℝ,
      planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) ≠ 0 ∧
        0 < ⟪A (planarHopfFlow t z), v⟫) :
    ∃ η : PlanarHopfSphere C → ℝ,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η ∧
      (∀ z, orbitAverage planarHopfFlow η z = 0) ∧
      (∀ z, orbitAverage planarHopfFlow (fun w ↦ η w ^ 2 • A w) z = 0) ∧
      ManifoldFlatOn (I := planarHopfModel C)
        (fun z ↦ η z - ‖f z‖ ^ 2 / 2) {z | planarOrbitCurvature planarHopfFlow f z = 0} := by
  obtain ⟨ηb, r, hb, hbmean, hbflat, hrflat, hrpos, _, hquad⟩ :=
    matrix_scalar_trial_exists f hf A hA hspan
  have hr := hrflat.1
  obtain ⟨δ, Mbound, hδ, hM, hinv⟩ := matrix_scalar_gram_uniform_inverse_bound
    f hf A hA ηb r hb hr hrpos hspan
  have hinverse : ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop, ∀ z : PlanarHopfSphere C,
      ∃ e : MatrixScalarCoefficients m ≃L[ℝ] MatrixScalarCoefficients m,
        e.toContinuousLinearMap = matrixScalarGram A (planarOrbitCurvature planarHopfFlow f)
          (matrixScalarOscillatoryBase f ηb r L) z ∧ ‖e.symm.toContinuousLinearMap‖ ≤ B := by
    refine ⟨Mbound, hM, ?_⟩
    filter_upwards [hinv] with L hL z
    exact (hL z).2
  obtain ⟨L, c, hc, hbasic, hroot⟩ :=
    matrix_scalar_small_correction f hf A hA ηb r hb hr hbmean hquad hinverse
  let κ := planarOrbitCurvature planarHopfFlow f
  let u := matrixScalarOscillatoryBase f ηb r L
  let η := fun z ↦ matrixScalarAnsatz A κ u (c z) z
  have ht := (matrix_planar_data_contMDiff f hf.smooth).2.1
  have hcos : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ Real.cos (L * orbitDeriv planarHopfFlow f z 1)) :=
    Real.contDiff_cos.contMDiff.comp (contMDiff_const.mul ht)
  have hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ u := hb.add (hr.mul hcos)
  obtain ⟨hη, hmean, hηquad, hcorrflat⟩ := matrix_scalar_moments_of_basic_root
    A hA κ u hf.curvature_smooth hu c hc hbasic hroot
  have htrialflat : ManifoldFlatOn (I := planarHopfModel C)
      (fun z ↦ u z - ηb z) {z | κ z = 0} := by
    have h := manifold_flat_on_smul hrflat
      (fun z ↦ Real.cos (L * orbitDeriv planarHopfFlow f z 1)) hcos
    simpa only [u, matrixScalarOscillatoryBase, add_sub_cancel_left, smul_eq_mul] using h
  have hsum := manifold_flat_on_add (manifold_flat_on_add hcorrflat htrialflat) hbflat
  change ManifoldFlatOn (I := planarHopfModel C)
    (fun z ↦ ((η z - u z) + (u z - ηb z)) + (ηb z - ‖f z‖ ^ 2 / 2))
    {z | planarOrbitCurvature planarHopfFlow f z = 0} at hsum
  have he : (fun z ↦ ((η z - u z) + (u z - ηb z)) + (ηb z - ‖f z‖ ^ 2 / 2)) =
      (fun z ↦ η z - ‖f z‖ ^ 2 / 2) := by
    funext z
    ring
  rw [he] at hsum
  exact ⟨η, hη, hmean, hηquad, hsum⟩

#print axioms matrix_scalar_moment

end GlobalEmbedding.Paper
