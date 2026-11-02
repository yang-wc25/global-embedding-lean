import GlobalEmbedding.Paper.PlanarHopfAverageCalculus
import GlobalEmbedding.Paper.MatrixAngleAnsatz
import GlobalEmbedding.Paper.MatrixManifoldFlatCurvatureCutoff
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The actual zero-mean scalar base for the matrix construction

Source: `main.tex`, `prop:matrix`, line355.
DAG: `matrix-scalar-base`.
The denominator is the actual positive period average of the actual cutoff.
No desired scalar solution, flatness or zero average is assumed.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The original paraboloid scalar potential |f|²/2.
Source: `prop:matrix`, lines285 and355. -/
def matrixScalarPotential {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) : ℝ := ‖f z‖ ^ 2 / 2

/-- The literal original η_b, normalized by the actual cutoff period integral.
Source: `prop:matrix`, line355. -/
def matrixScalarBase {C : ℕ} (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) : ℝ :=
  matrixScalarPotential f z - matrixAngleCutoff κ z *
    (orbitAverage planarHopfFlow (matrixScalarPotential f) z /
      orbitAverage planarHopfFlow (matrixAngleCutoff κ) z)

/-- The actual paraboloid potential is native smooth by its genuine coordinate
quadratic formula. Source: `prop:matrix`, line355. -/
theorem matrixScalarPotential_contMDiff {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixScalarPotential f) := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contMDiff.comp hf
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contMDiff.comp hf
  have he : matrixScalarPotential f = fun z ↦ (f z 0 ^ 2 + f z 1 ^ 2) / 2 := by
    funext z
    simp only [matrixScalarPotential, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [he]
  exact ((h0.pow 2).add (h1.pow 2)).div_const (c := (2 : ℝ))

/-- The actual η_b is native smooth, has zero actual period average, and differs
from the original paraboloid potential by a function flat in every native smooth
chart, to every order including zero.

Proof: the cutoff average is strictly positive by the actual Hopf average
positivity theorem. Both actual averages are native smooth and basic. Their
ratio is therefore a genuine smooth basic function. Its cutoff multiple is
fully flat by the accepted native cutoff theorem. Pull the basic ratio out of
the actual period integral; it cancels the potential average exactly.
Source: `prop:matrix`, line355. -/
theorem matrixScalarBase_properties {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (κ : PlanarHopfSphere C → ℝ)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (hn : ∀ z, ∃ s : ℝ, κ (planarHopfFlow s z) ≠ 0) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixScalarBase f κ) ∧
    (∀ z, orbitAverage planarHopfFlow (matrixScalarBase f κ) z = 0) ∧
    ManifoldFlatOn (I := planarHopfModel C)
      (fun z ↦ matrixScalarBase f κ z - matrixScalarPotential f z) {z | κ z = 0} := by
  have hφ := matrixScalarPotential_contMDiff f hf
  have hu : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixAngleCutoff κ) :=
    (manifold_flat_curvature_cutoff κ hκ).1
  have hp (z : PlanarHopfSphere C) :
      0 < orbitAverage planarHopfFlow (matrixAngleCutoff κ) z :=
    planarHopfAverage_cutoff_pos κ hκ hn z
  have hc : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ orbitAverage planarHopfFlow (matrixScalarPotential f) z /
        orbitAverage planarHopfFlow (matrixAngleCutoff κ) z) :=
    (planarHopfAverage_contMDiff _ hφ).div₀ (planarHopfAverage_contMDiff _ hu)
      (fun z ↦ (hp z).ne')
  refine ⟨hφ.sub (hu.mul hc), ?_, ?_⟩
  · intro z
    have hR : Continuous (fun t : ℝ ↦ planarHopfFlow t z) :=
      (planarHopfFlow_contMDiff C).continuous.comp (continuous_id.prodMk continuous_const)
    change (∫ t in (0 : ℝ)..1,
      matrixScalarPotential f (planarHopfFlow t z) - matrixAngleCutoff κ (planarHopfFlow t z) *
        (orbitAverage planarHopfFlow (matrixScalarPotential f) (planarHopfFlow t z) /
          orbitAverage planarHopfFlow (matrixAngleCutoff κ) (planarHopfFlow t z))) = 0
    simp_rw [planarHopfAverage_flow]
    have hInt : IntervalIntegrable
        (fun t ↦ matrixAngleCutoff κ (planarHopfFlow t z) *
          (orbitAverage planarHopfFlow (matrixScalarPotential f) z /
            orbitAverage planarHopfFlow (matrixAngleCutoff κ) z))
        MeasureTheory.volume 0 1 :=
      ((hu.continuous.comp hR).mul continuous_const).intervalIntegrable 0 1
    have hIntφ : IntervalIntegrable
        (fun t ↦ matrixScalarPotential f (planarHopfFlow t z)) MeasureTheory.volume 0 1 :=
      (hφ.continuous.comp hR).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub hIntφ hInt, intervalIntegral.integral_mul_const]
    change orbitAverage planarHopfFlow (matrixScalarPotential f) z -
      orbitAverage planarHopfFlow (matrixAngleCutoff κ) z *
        (orbitAverage planarHopfFlow (matrixScalarPotential f) z /
          orbitAverage planarHopfFlow (matrixAngleCutoff κ) z) = 0
    have hz := (hp z).ne'
    field_simp [hz]
    ring
  · have hflat := manifold_flat_curvature_cutoff_smul κ hκ
      (fun z ↦ -(orbitAverage planarHopfFlow (matrixScalarPotential f) z /
        orbitAverage planarHopfFlow (matrixAngleCutoff κ) z)) hc.neg
    have he : (fun z ↦ matrixScalarBase f κ z - matrixScalarPotential f z) =
        (fun z ↦ expNegInvGlue (κ z ^ 2) •
          -(orbitAverage planarHopfFlow (matrixScalarPotential f) z /
            orbitAverage planarHopfFlow (matrixAngleCutoff κ) z)) := by
      funext z
      simp only [matrixScalarBase, matrixAngleCutoff, smul_eq_mul]
      ring
    rw [he]
    exact hflat

#print axioms matrixScalarPotential_contMDiff
#print axioms matrixScalarBase_properties

end GlobalEmbedding.Paper
