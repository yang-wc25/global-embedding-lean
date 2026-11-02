import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties
import GlobalEmbedding.Paper.PlanarOrbitPrimitive
import GlobalEmbedding.Paper.MatrixOrbitCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Genuine periodic real angles on actual Hopf orbits

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines327–332.
DAG node: `matrix-periodic-orbit-angle`.
-/
noncomputable section
open Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Paper

/-- The actual primitive of the original canonical curvature. This does not choose
an unrelated angular correction or a global argument. -/
def matrixCurvaturePrimitive {C : ℕ} (f : PlanarHopfSphere C → Planar) :
    PlanarHopfSphere C → ℝ :=
  planarOrbitPrimitive planarHopfFlow (planarOrbitCurvature planarHopfFlow f)

/-- The actual curvature has zero average, by its genuine half-period oddness. -/
theorem matrix_curvature_average_zero {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (z : PlanarHopfSphere C) :
    orbitAverage planarHopfFlow (planarOrbitCurvature planarHopfFlow f) z = 0 := by
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth
  have hd (x : PlanarHopfSphere C) : Differentiable ℝ (fun t : ℝ ↦ f (planarHopfFlow t x)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add f hf.smooth t x).differentiableAt
  have hvd (x : PlanarHopfSphere C) : Differentiable ℝ
      (fun t : ℝ ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t x)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add _ hv t x).differentiableAt
  have hodd (x : PlanarHopfSphere C) := planarOrbitCurvature_half_odd
    planarHopfFlow planarHopfFlow_add planarHopfFlow_zero f hd hvd
    (fun w ↦ by rw [planarHopfFlow_half]; exact hf.reflection w) x
  exact matrix_orbitAverage_half_odd_zero planarHopfFlow planarHopfFlow_add
    planarHopfFlow_one (planarOrbitCurvature planarHopfFlow f) hodd z

/-- The genuine curvature primitive is native smooth on the entire actual sphere. -/
theorem matrixCurvaturePrimitive_contMDiff {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixCurvaturePrimitive f) :=
  planarOrbitPrimitive_contMDiff planarHopfFlow
    ((planarHopfFlow_contMDiff C).comp (contMDiff_snd.prodMk contMDiff_fst))
    _ hf.curvature_smooth

/-- This actual primitive differentiates to the actual canonical curvature. -/
theorem matrixCurvaturePrimitive_orbitDeriv {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow (matrixCurvaturePrimitive f) z =
      planarOrbitCurvature planarHopfFlow f z :=
  planarOrbitPrimitive_orbitDeriv_of_average_zero planarHopfFlow planarHopfFlow_zero
    planarHopfFlow_add planarHopfFlow_one _ z
    ((hf.curvature_smooth.comp ((planarHopfFlow_contMDiff C).comp
      (contMDiff_id.prodMk contMDiff_const))).continuous)
    (matrix_curvature_average_zero f hf z)

/-- A true unit planar rotation ODE and a genuine periodic real curvature primitive
produce an actual periodic angle. Only the ordinary argument of one constant unit
complex number is used, so no global smooth argument is assumed. -/
private theorem unit_planar_ode_periodic_angle
    (s q κ ψ : ℝ → ℝ) (hunit : ∀ t, s t ^ 2 + q t ^ 2 = 1)
    (hs : ∀ t, HasDerivAt s (-κ t * q t) t)
    (hq : ∀ t, HasDerivAt q (κ t * s t) t)
    (hψ : ∀ t, HasDerivAt ψ (κ t) t)
    (hψc : ContDiff ℝ 1 ψ) (hψp : Function.Periodic ψ 1) :
    ∃ α : ℝ → ℝ, ContDiff ℝ 1 α ∧ Function.Periodic α 1 ∧
      (∀ t, HasDerivAt α (κ t) t) ∧
      (∀ t, s t = Real.cos (α t) ∧ q t = Real.sin (α t)) := by
  let w₀ : ℝ → ℝ := fun t ↦ Real.cos (ψ t) * s t + Real.sin (ψ t) * q t
  let w₁ : ℝ → ℝ := fun t ↦ -Real.sin (ψ t) * s t + Real.cos (ψ t) * q t
  have hw₀ (t : ℝ) : HasDerivAt w₀ 0 t := by
    convert (((hψ t).cos.mul (hs t)).add ((hψ t).sin.mul (hq t))) using 1
    ring
  have hw₁ (t : ℝ) : HasDerivAt w₁ 0 t := by
    convert ((((hψ t).sin.neg).mul (hs t)).add ((hψ t).cos.mul (hq t))) using 1
    simp only [Pi.neg_apply]
    ring
  have hc₀ (t : ℝ) : w₀ t = w₀ 0 :=
    is_const_of_deriv_eq_zero (fun t ↦ (hw₀ t).differentiableAt)
      (fun t ↦ (hw₀ t).deriv) t 0
  have hc₁ (t : ℝ) : w₁ t = w₁ 0 :=
    is_const_of_deriv_eq_zero (fun t ↦ (hw₁ t).differentiableAt)
      (fun t ↦ (hw₁ t).deriv) t 0
  have hwnorm : w₀ 0 ^ 2 + w₁ 0 ^ 2 = 1 := by
    dsimp only [w₀, w₁]
    nlinarith [Real.sin_sq_add_cos_sq (ψ 0), hunit 0]
  let Z : ℂ := (w₀ 0 : ℂ) + (w₁ 0 : ℂ) * Complex.I
  have hZ : ‖Z‖ = 1 := by
    rw [Complex.norm_add_mul_I, hwnorm, Real.sqrt_one]
  have hcos : Real.cos (Complex.arg Z) = w₀ 0 := by
    have h := Complex.norm_mul_cos_arg Z
    simpa only [hZ, one_mul, Z, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero] using h
  have hsin : Real.sin (Complex.arg Z) = w₁ 0 := by
    have h := Complex.norm_mul_sin_arg Z
    simpa only [hZ, one_mul, Z, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
      zero_mul, add_zero, zero_add] using h
  refine ⟨fun t ↦ ψ t + Complex.arg Z, hψc.add contDiff_const,
    (fun t ↦ by dsimp only; rw [hψp]), (fun t ↦ (hψ t).add_const _), ?_⟩
  intro t
  rw [Real.cos_add, Real.sin_add, hcos, hsin, ← hc₀ t, ← hc₁ t]
  dsimp only [w₀, w₁]
  constructor
  · calc
      s t = (Real.cos (ψ t) ^ 2 + Real.sin (ψ t) ^ 2) * s t := by
        rw [Real.cos_sq_add_sin_sq, one_mul]
      _ = _ := by ring
  · calc
      q t = (Real.cos (ψ t) ^ 2 + Real.sin (ψ t) ^ 2) * q t := by
        rw [Real.cos_sq_add_sin_sq, one_mul]
      _ = _ := by ring

/-- The same actual whole-sphere planar selector has a genuine periodic real angle
on each actual Hopf orbit, with true derivative kappa and true velocity components.
The angle is nonconstant by the original actual curvature signs. -/
theorem matrix_planar_periodic_orbit_angle {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (z : PlanarHopfSphere C) :
    ∃ α : ℝ → ℝ, ContDiff ℝ 1 α ∧ Function.Periodic α 1 ∧
      (∀ t, HasDerivAt α (planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z)) t) ∧
      (∀ t, orbitDeriv planarHopfFlow f (planarHopfFlow t z) 0 = Real.cos (α t) ∧
        orbitDeriv planarHopfFlow f (planarHopfFlow t z) 1 = Real.sin (α t)) ∧
      (∃ x y, α x ≠ α y) := by
  let s : ℝ → ℝ := fun t ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t z) 0
  let q : ℝ → ℝ := fun t ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t z) 1
  let κ : ℝ → ℝ := fun t ↦ planarOrbitCurvature planarHopfFlow f (planarHopfFlow t z)
  let ψ : ℝ → ℝ := fun t ↦ matrixCurvaturePrimitive f (planarHopfFlow t z)
  have hv := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) f hf.smooth
  have hvd (w : PlanarHopfSphere C) : Differentiable ℝ
      (fun t : ℝ ↦ orbitDeriv planarHopfFlow f (planarHopfFlow t w)) :=
    fun t ↦ (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add _ hv t w).differentiableAt
  have hunit (t : ℝ) : s t ^ 2 + q t ^ 2 = 1 := by
    have hn := congrArg (fun r : ℝ ↦ r ^ 2) (hf.unit_speed (planarHopfFlow t z))
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow, s, q] using hn
  have hs (t : ℝ) : HasDerivAt s (-κ t * q t) t := by
    have hh := planarOrbitCoordinate_hasDerivAt planarHopfFlow planarHopfFlow_add
      (orbitDeriv planarHopfFlow f) hvd z t 0
    rw [hf.acceleration] at hh
    simpa only [s, κ, q, PiLp.smul_apply, smul_eq_mul,
      planarQuarterTurn_apply_zero, mul_neg, neg_mul] using hh
  have hq (t : ℝ) : HasDerivAt q (κ t * s t) t := by
    have hh := planarOrbitCoordinate_hasDerivAt planarHopfFlow planarHopfFlow_add
      (orbitDeriv planarHopfFlow f) hvd z t 1
    rw [hf.acceleration] at hh
    simpa only [s, κ, q, PiLp.smul_apply, smul_eq_mul,
      planarQuarterTurn_apply_one] using hh
  have hψnative := matrixCurvaturePrimitive_contMDiff f hf
  have hψsmooth : ContDiff ℝ ∞ ψ :=
    (hψnative.comp ((planarHopfFlow_contMDiff C).comp
      (contMDiff_id.prodMk contMDiff_const))).contDiff
  have hψd (t : ℝ) : HasDerivAt ψ (κ t) t := by
    have hh := hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
      planarHopfFlow_add (matrixCurvaturePrimitive f) hψnative t z
    rwa [matrixCurvaturePrimitive_orbitDeriv f hf] at hh
  have hψp : Function.Periodic ψ 1 :=
    orbitMap_periodic planarHopfFlow planarHopfFlow_add planarHopfFlow_one
      (matrixCurvaturePrimitive f) z
  obtain ⟨α, hα, hp, hd, hvα⟩ := unit_planar_ode_periodic_angle s q κ ψ hunit hs hq hψd
    (hψsmooth.of_le (by simp)) hψp
  refine ⟨α, hα, hp, hd, hvα, ?_⟩
  by_contra hbad
  push Not at hbad
  have heq : α = fun _ ↦ α 0 := funext (fun t ↦ hbad t 0)
  obtain ⟨tn, tp, _, hpos⟩ := hf.curvature_signs z
  have hh := hd tp
  rw [heq] at hh
  have hz := hh.unique (hasDerivAt_const tp (α 0))
  exact hpos.ne' hz

end GlobalEmbedding.Paper
