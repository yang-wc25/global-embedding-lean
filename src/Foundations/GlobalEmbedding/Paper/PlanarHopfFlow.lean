import GlobalEmbedding.Paper.PlanarHopfSphere
import GlobalEmbedding.Paper.PlanarPeriodOneCalculus

/-!
# The literal period-one Hopf action on the genuine complex sphere

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, lines245–266.
DAG node: `planar-hopf-flow`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The source's actual period-one Hopf flow, with the normalization 2π in its exponent. -/
def planarHopfFlow {C : ℕ} (t : ℝ) (z : PlanarHopfSphere C) : PlanarHopfSphere C :=
  ⟨(Circle.exp (2 * Real.pi * t) : ℂ) • (z : PlanarHopfAmbient C),
    mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Circle.norm_coe, mem_sphere_zero_iff_norm.mp z.property, one_mul])⟩

/-- The literal ambient value is multiplication by exp(2πit). -/
theorem planarHopfFlow_coe {C : ℕ} (t : ℝ) (z : PlanarHopfSphere C) :
    (planarHopfFlow t z : PlanarHopfAmbient C) =
      Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) • (z : PlanarHopfAmbient C) := rfl

@[simp] theorem planarHopfFlow_zero {C : ℕ} (z : PlanarHopfSphere C) :
    planarHopfFlow 0 z = z := by
  apply Subtype.ext
  simp [planarHopfFlow]

/-- Actual flow addition follows from the genuine exponential homomorphism and scalar action. -/
theorem planarHopfFlow_add {C : ℕ} (s t : ℝ) (z : PlanarHopfSphere C) :
    planarHopfFlow (s + t) z = planarHopfFlow s (planarHopfFlow t z) := by
  apply Subtype.ext
  change (Circle.exp (2 * Real.pi * (s + t)) : ℂ) • (z : PlanarHopfAmbient C) =
    (Circle.exp (2 * Real.pi * s) : ℂ) •
      ((Circle.exp (2 * Real.pi * t) : ℂ) • (z : PlanarHopfAmbient C))
  rw [mul_add, Circle.exp_add, Circle.coe_mul, mul_smul]

@[simp] theorem planarHopfFlow_one {C : ℕ} (z : PlanarHopfSphere C) :
    planarHopfFlow 1 z = z := by
  apply Subtype.ext
  change Complex.exp ((2 * Real.pi * (1 : ℝ) : ℝ) * Complex.I) •
    (z : PlanarHopfAmbient C) = _
  simp [Complex.exp_two_pi_mul_I]

/-- Half of the period is exactly the original antipodal map, not a chosen orbit origin. -/
theorem planarHopfFlow_half {C : ℕ} (z : PlanarHopfSphere C) :
    planarHopfFlow (1 / 2 : ℝ) z = -z := by
  apply Subtype.ext
  change Complex.exp ((2 * Real.pi * (1 / 2 : ℝ) : ℝ) * Complex.I) •
    (z : PlanarHopfAmbient C) = -(z : PlanarHopfAmbient C)
  have h : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [h]
  simp only [Complex.exp_pi_mul_I,
    neg_smul, one_smul]

/-- Every actual orbit is period one, including all low-dimensional and empty sphere cases. -/
theorem planarHopfFlow_periodic {C : ℕ} (z : PlanarHopfSphere C) :
    Function.Periodic (fun t : ℝ ↦ planarHopfFlow t z) 1 := by
  intro t
  change planarHopfFlow (t + 1) z = planarHopfFlow t z
  rw [planarHopfFlow_add, planarHopfFlow_one]

/-- Joint native smoothness is obtained from actual complex exponential/scalar multiplication
and the genuine native sphere codomain criterion. No smooth action is assumed as input. -/
theorem planarHopfFlow_contMDiff (C : ℕ) [Fact (0 < C)] :
    ContMDiff (𝓘(ℝ, ℝ).prod (planarHopfModel C)) (planarHopfModel C) ∞
      (fun p : ℝ × PlanarHopfSphere C ↦ planarHopfFlow p.1 p.2) := by
  apply ContMDiff.codRestrict_sphere
  have he : ContDiff ℝ ∞ (fun t : ℝ ↦
      Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) :=
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
      contDiff_const).cexp
  have hs := he.contMDiff.comp
    (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod (planarHopfModel C)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × PlanarHopfSphere C ↦ p.1))
  have hz := (planarHopfSphere_contMDiff_coe C).comp
    (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod (planarHopfModel C))
      (planarHopfModel C) ∞ (fun p : ℝ × PlanarHopfSphere C ↦ p.2))
  have hm : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, PlanarHopfAmbient C))
      𝓘(ℝ, PlanarHopfAmbient C) ∞
      (fun p : ℂ × PlanarHopfAmbient C ↦ p.1 • p.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contDiff_smul.contMDiff
  exact hm.comp (hs.prodMk hz)

/-- The genuine Hopf flow supplies the shared actual period-one smooth-flow data.
Every field is proved above; no selector, formal derivative or desired inverse is an input. -/
def planarHopfSmoothFlow (C : ℕ) [Fact (0 < C)] :
    PeriodOneSmoothFlow (planarHopfModel C) (PlanarHopfSphere C) where
  flow := planarHopfFlow
  flow_zero := planarHopfFlow_zero
  flow_add := planarHopfFlow_add
  flow_one := planarHopfFlow_one
  smooth := planarHopfFlow_contMDiff C

end GlobalEmbedding.Paper
