import GlobalEmbedding.Paper.PlanarHopfFlow
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The genuine native Hopf generator

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines245–266.
DAG node: `planar-hopf-generator`.
-/

noncomputable section
open Manifold
open Bundle (TotalSpace)
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Apply the actual tangent map of the smooth Hopf action to the time-unit tangent vector.
This construction uses the genuine tangent bundle rather than a supplied vector field. -/
def planarHopfTangentLift (C : ℕ) [Fact (0 < C)]
    (z : PlanarHopfSphere C) : TangentBundle (planarHopfModel C) (PlanarHopfSphere C) :=
  tangentMap (𝓘(ℝ, ℝ).prod (planarHopfModel C)) (planarHopfModel C)
    (fun p : ℝ × PlanarHopfSphere C ↦ planarHopfFlow p.1 p.2)
    ((equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ (planarHopfModel C) (PlanarHopfSphere C)).symm
      (TotalSpace.mk' ℝ 0 (1 : ℝ), TotalSpace.mk'
        (EuclideanSpace ℝ (Fin (2 * C - 1))) z 0))

/-- Genuine native tangent-map smoothness gives a smooth total-space generator lift. -/
theorem planarHopfTangentLift_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (planarHopfModel C) (planarHopfModel C).tangent ∞
      (planarHopfTangentLift C) := by
  exact ((planarHopfFlow_contMDiff C).contMDiff_tangentMap (by simp)).comp
    (contMDiff_equivTangentBundleProd_symm.comp
      (contMDiff_const.prodMk (Bundle.contMDiff_zeroSection ℝ
        (TangentSpace (planarHopfModel C) : PlanarHopfSphere C → Type _))))

/-- Its base point is the original sphere point, by the actual flow-zero identity. -/
theorem planarHopfTangentLift_base (C : ℕ) [Fact (0 < C)] (z : PlanarHopfSphere C) :
    (planarHopfTangentLift C z).proj = z := planarHopfFlow_zero z

/-- The actual tangent generator is the fiber component of the genuine tangent lift. -/
def planarHopfGenerator {C : ℕ} [Fact (0 < C)] (z : PlanarHopfSphere C) :
    TangentSpace (planarHopfModel C) z :=
  cast (congrArg (TangentSpace (planarHopfModel C)) (planarHopfTangentLift_base C z))
    (planarHopfTangentLift C z).2

/-- The generator has exactly the original smooth total-space lift. -/
theorem planarHopfGenerator_totalSpace (C : ℕ) [Fact (0 < C)] (z : PlanarHopfSphere C) :
    TotalSpace.mk' (EuclideanSpace ℝ (Fin (2 * C - 1))) z (planarHopfGenerator z) =
      planarHopfTangentLift C z :=
  TotalSpace.mk_cast (planarHopfTangentLift_base C z) _

/-- The actual Hopf generator is a smooth native tangent section. -/
def planarHopfGeneratorSection (C : ℕ) [Fact (0 < C)] :
    ContMDiffSection (planarHopfModel C) (EuclideanSpace ℝ (Fin (2 * C - 1))) ∞
      (TangentSpace (planarHopfModel C) : PlanarHopfSphere C → Type _) where
  toFun := planarHopfGenerator
  contMDiff_toFun := by
    simpa only [planarHopfGenerator_totalSpace] using planarHopfTangentLift_contMDiff C

/-- The constructed native vector is the genuine orbit mfderiv at time zero. -/
theorem planarHopfGenerator_eq_orbit_mfderiv (C : ℕ) [Fact (0 < C)]
    (z : PlanarHopfSphere C) :
    planarHopfGenerator z =
      cast (congrArg (TangentSpace (planarHopfModel C)) (planarHopfFlow_zero z))
        (mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C)
          (fun t : ℝ ↦ planarHopfFlow t z) 0 (1 : ℝ)) := by
  have h := mfderiv_comp (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, ℝ).prod (planarHopfModel C)) (I'' := planarHopfModel C)
    (f := fun t : ℝ ↦ (t, z))
    (g := fun p : ℝ × PlanarHopfSphere C ↦ planarHopfFlow p.1 p.2) (x := 0)
    ((planarHopfFlow_contMDiff C).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  rw [mfderiv_prod_left] at h
  unfold planarHopfGenerator
  congr 1
  change mfderiv (𝓘(ℝ, ℝ).prod (planarHopfModel C)) (planarHopfModel C)
    (fun p : ℝ × PlanarHopfSphere C ↦ planarHopfFlow p.1 p.2) (0, z) (1, 0) = _
  exact (congrArg (fun L ↦ L (1 : ℝ)) h).symm

/-- Actual differentiation of the ambient orbit yields the prescribed 2π-normalized
complex velocity. Only actual exponential and scalar-product derivative rules are used. -/
theorem planarHopfOrbit_hasDerivAt {C : ℕ} (z : PlanarHopfSphere C) :
    HasDerivAt (fun t : ℝ ↦ (planarHopfFlow t z : PlanarHopfAmbient C))
      ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)) 0 := by
  have ha : HasDerivAt (fun t : ℝ ↦ 2 * Real.pi * t) (2 * Real.pi) 0 :=
    by simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.pi)
  have hc : HasDerivAt (fun t : ℝ ↦ ((2 * Real.pi * t : ℝ) : ℂ))
      ((2 * Real.pi : ℝ) : ℂ) 0 :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ha
  simpa only [planarHopfFlow_coe, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul] using (hc.mul_const Complex.I).cexp.smul_const
      (z : PlanarHopfAmbient C)

/-- The native generator derivative of every actual smooth vector-valued observable is
exactly the shared actual one-variable orbit derivative, with the same time normalization. -/
theorem planarHopfGenerator_mvfderiv {C : ℕ} [Fact (0 < C)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : PlanarHopfSphere C → F)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, F) ∞ f) (z : PlanarHopfSphere C) :
    mvfderiv (planarHopfModel C) f z (planarHopfGenerator z) =
      orbitDeriv planarHopfFlow f z := by
  have horbit : MDifferentiableAt 𝓘(ℝ, ℝ) (planarHopfModel C)
      (fun t : ℝ ↦ planarHopfFlow t z) 0 :=
    (((planarHopfFlow_contMDiff C).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp))
  have h := mvfderiv_comp (I := planarHopfModel C) (I' := 𝓘(ℝ, ℝ)) 0
    (hf.mdifferentiableAt (by simp)) horbit
  have he := congrArg (fun T : ℝ →L[ℝ] F ↦ T (1 : ℝ)) h
  rw [mvfderiv_eq_fderiv] at he
  change fderiv ℝ (fun t : ℝ ↦ f (planarHopfFlow t z)) 0 (1 : ℝ) =
    mvfderiv (planarHopfModel C) f (planarHopfFlow 0 z)
      (mfderiv 𝓘(ℝ, ℝ) (planarHopfModel C)
        (fun t : ℝ ↦ planarHopfFlow t z) 0 (1 : ℝ)) at he
  rw [planarHopfFlow_zero] at he
  rw [planarHopfGenerator_eq_orbit_mfderiv]
  exact he.symm

/-- The actual native generator pushes into the original ambient space as 2πiz. -/
theorem planarHopfGenerator_ambient {C : ℕ} [Fact (0 < C)] (z : PlanarHopfSphere C) :
    mvfderiv (planarHopfModel C) (fun w : PlanarHopfSphere C ↦ (w : PlanarHopfAmbient C))
      z (planarHopfGenerator z) =
      ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • (z : PlanarHopfAmbient C)) := by
  rw [planarHopfGenerator_mvfderiv _ (planarHopfSphere_contMDiff_coe C)]
  exact (planarHopfOrbit_hasDerivAt z).deriv

/-- The true Hopf generator never vanishes. Its genuine ambient derivative is a nonzero
complex scalar times a norm-one vector, so zero cannot be its native tangent value. -/
theorem planarHopfGenerator_ne_zero {C : ℕ} [Fact (0 < C)] (z : PlanarHopfSphere C) :
    planarHopfGenerator z ≠ 0 := by
  intro hz
  have he := planarHopfGenerator_ambient z
  rw [hz, map_zero] at he
  have hscalar : (((2 * Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))
      Complex.I_ne_zero
  exact (smul_ne_zero hscalar (ne_zero_of_mem_unit_sphere z)) he.symm

/-- The period-one normalization gives actual ambient speed 2π, uniformly on the sphere. -/
theorem planarHopfGenerator_ambient_norm {C : ℕ} [Fact (0 < C)]
    (z : PlanarHopfSphere C) :
    ‖mvfderiv (planarHopfModel C)
      (fun w : PlanarHopfSphere C ↦ (w : PlanarHopfAmbient C)) z (planarHopfGenerator z)‖ =
      2 * Real.pi := by
  rw [planarHopfGenerator_ambient]
  simp [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos),
    mem_sphere_zero_iff_norm.mp z.property]

end GlobalEmbedding.Paper
