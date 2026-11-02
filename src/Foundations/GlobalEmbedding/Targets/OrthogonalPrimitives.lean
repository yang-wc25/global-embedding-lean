import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import GlobalEmbedding.Paper.ManifoldFlatOn
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Normed
import GlobalEmbedding.Paper.MatrixCorrectedAngle
import GlobalEmbedding.Paper.MatrixAngularCone
import GlobalEmbedding.Paper.MatrixOrthogonalPrimitives
import GlobalEmbedding.Paper.MatrixScalarMoment
import GlobalEmbedding.Paper.PlanarFlatSecondJet

/-!
# Orthogonal primitives and scalar moments on the actual Hopf sphere

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:matrix`, lines272–366. DAG: `prop-matrix`.
This is the full original statement for all C≥2 and d≥2. Derivatives, period
integrals, SO(d) and full native manifold flatness are the actual objects.
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace GlobalEmbedding.Paper

local instance matrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The full original orthogonal-primitive and scalar-moment construction.

Proof plan: choose the actual analytic unit-speed reflected planar selector.
For the SO(3) block correct θ₀=Tt by actual cutoff-weighted four-moment
variations. Uniform oscillatory averaging makes the residual tend to zero and
the derivative Gram tend to positive weighted profile blocks. The accepted
small-root theorem gives smooth basic coefficients, oddness, full flatness of
the angle correction and the original scaled C1 error. Opposite regular angle
branches and quarter-turn samples give an actual uniformly positive angular
cone for sufficiently large T. The actual oriented Q₃ frame has zero mean;
its actual period primitive P₃ has average P₃ᵀQ₃ zero by skewness, reflection
and the fourth angle equation. The literal two-dimensional complex block
supplies every even dimension; one three-block and repeated two-blocks supply
every odd dimension. Thus Q=XP lies in SO(d), satisfies both matrix periods,
and XQ=0 on zero curvature. In its fixed skew-block space the actual A=QᵀXQ
has positive orbit cone away from zero curvature. Finite smooth bumps and the
unique minimizer of a coercive strictly convex exponential potential realize
any smooth basic A-moment by an actual nonnegative flat density with smooth
flat square root. Start with η_b=|f|²/2−ρ₀ av(|f|²/2)/avρ₀. Choose the density
moment to cancel av(Aη_b²); add sqrt(2ρ)cos(Lt). Oscillatory averaging makes
both scalar constraints small. Their actual cutoff-weighted coefficient Gram
converges to a positive operator, while coefficient Hessians are uniformly
bounded. The accepted correction theorem yields actual smooth basic small
coefficients and hence η satisfying both exact scalar moments. Every change
from |f|²/2 is fully flat on zero curvature. The full second jet there and
X²f=κJ₂Xf, |Xf|=1 give X²η=1. No desired angle, cone, density or solution is
assumed by this theorem.
Source: `prop:matrix`, complete statement and proof, lines272–366. -/
theorem orthogonal_primitives_scalar_moments (C d : ℕ) (hC : 2 ≤ C) (hd : 2 ≤ d) :
    letI : Fact (0 < C) := ⟨by omega⟩
    ∃ f : PlanarHopfSphere C → Planar,
    ∃ P : PlanarHopfSphere C → Matrix (Fin d) (Fin d) ℝ,
    ∃ η : PlanarHopfSphere C → ℝ,
      MatrixPlanarSelectorProperties f ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin d) (Fin d) ℝ) ∞ P ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η ∧
      let Q := orbitDeriv planarHopfFlow P
      (∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ) ∧
      (∀ z, orbitAverage planarHopfFlow Q z = 0) ∧
      (∀ z, orbitAverage planarHopfFlow (fun w ↦ (P w).transpose * Q w) z = 0) ∧
      (∀ z, orbitAverage planarHopfFlow η z = 0) ∧
      (∀ z, orbitAverage planarHopfFlow
        (fun w ↦ η w ^ 2 • ((Q w).transpose * orbitDeriv planarHopfFlow Q w)) z = 0) ∧
      (∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
        orbitDeriv planarHopfFlow Q z = 0) ∧
      ManifoldFlatOn (I := planarHopfModel C)
        (fun z ↦ η z - ‖f z‖ ^ 2 / 2) {z | planarOrbitCurvature planarHopfFlow f z = 0} ∧
      (∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
        orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1) := by
  let _ : Fact (0 < C) := ⟨by omega⟩
  obtain ⟨f, hf⟩ := matrix_planar_selector_exists C hC
  obtain ⟨θ, hθ, _, hθzero, hmom, herr, _⟩ := matrixCorrectedAngleFamily_exists
    f hf.smooth hf.unit_speed hf.reflection hf.orbit_analytic
  have he : ∀ ε > 0, ∀ᶠ T : ℝ in Filter.atTop, ∀ w,
      |θ T w - T * matrixPlanarT f w| + T⁻¹ *
        |orbitDeriv planarHopfFlow (fun z ↦ θ T z - T * matrixPlanarT f z) w| ≤ ε := by
    intro ε hε
    have hh := (Metric.tendstoUniformly_iff.mp herr) ε hε
    filter_upwards [hh] with T hT w
    have hv : abs (|θ T w - T * matrixPlanarT f w| + T⁻¹ *
        |orbitDeriv planarHopfFlow (fun z ↦ θ T z - T * matrixPlanarT f z) w|) ≤ ε := by
      simpa only [matrixPlanarT, Real.dist_eq, zero_sub, abs_neg] using (hT w).le
    exact (le_abs_self _).trans hv
  have hcone := matrix_angular_cone f hf θ (Filter.Eventually.of_forall hθ) he
  obtain ⟨T, hT, hMT, hCT⟩ :=
    ((Filter.eventually_ge_atTop (1 : ℝ)).and (hmom.and hcone)).exists
  obtain ⟨hodd, hM⟩ := hMT
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  obtain ⟨P, j, hP, hSO, hQmean, hPperiod, hzero, hj⟩ :=
    matrix_hopf_orthogonal_primitives f hf (θ T) (hθ T) hodd
      (fun z ↦ (hM z).1) (fun z ↦ (hM z).2.1)
      (fun z ↦ (hM z).2.2.1) (fun z ↦ (hM z).2.2.2)
      (hθzero T) T hTp.ne' d hd
  let A : PlanarHopfSphere C → MatrixAngularSpace := fun z ↦
    matrixAngularVector (planarOrbitCurvature planarHopfFlow f z)
      (θ T z) (T⁻¹ * orbitDeriv planarHopfFlow (θ T) z)
  have hA : ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngularSpace) ∞ A :=
    matrix_hopf_angular_coordinates_contMDiff f hf (θ T) (hθ T) T
  have hspan : ∀ z, ∀ v : MatrixAngularSpace, v ≠ 0 → ∃ t : ℝ,
      planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z) ≠ 0 ∧
        0 < inner ℝ (A (planarHopfFlow t z)) v := by
    intro z v hv
    obtain ⟨t, hk, hp⟩ := hCT z v hv
    refine ⟨t, hk, ?_⟩
    rw [real_inner_comm]
    exact hp
  obtain ⟨η, hη, hηmean, hηquadratic, hflat⟩ := matrix_scalar_moment f hf A hA hspan
  refine ⟨f, P, η, hf, hP, hη, hSO, hQmean, hPperiod, hηmean, ?_, hzero, hflat, ?_⟩
  · intro z
    exact matrix_hopf_angular_quadratic_moment_transport A hA
      (orbitDeriv planarHopfFlow P) j hj η hη z (hηquadratic z)
  · intro z hz
    exact planar_flat_second_jet f hf η hflat z hz

#print axioms orthogonal_primitives_scalar_moments

end GlobalEmbedding.Paper
