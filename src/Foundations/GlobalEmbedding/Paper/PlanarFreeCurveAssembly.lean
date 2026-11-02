import GlobalEmbedding.Paper.PlanarFreeCurve
import GlobalEmbedding.Paper.PlanarUnitBinormal
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual global freeness of the paraboloid lift along the common flow

Source: `main.tex`, `lem:planar`, line 265.
DAG parent: `planar-free-curve` (still open until actual speed normalization).
This identifies the actual first and iterated common orbit derivatives of the
actual global lift, preparing the nonzero-speed input for W4 normalization.
-/

noncomputable section
open scoped Manifold ContDiff InnerProductSpace

namespace GlobalEmbedding.Paper

/-- The actual global paraboloid lift is free for the same actual common flow.
All intermediate real jets are genuine derivatives of the actual orbit map. -/
theorem planarQuadraticLift_orbit_free {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun t ↦ f (R t x)))
    (hv : ∀ x, Differentiable ℝ (fun t ↦ orbitDeriv R f (R t x)))
    (hunit : ∀ x, ‖orbitDeriv R f x‖ = 1) (x : M) :
    LinearIndependent ℝ ![orbitDeriv R (fun y ↦ planarQuadraticLift (f y)) x,
      orbitDeriv R (orbitDeriv R (fun y ↦ planarQuadraticLift (f y))) x] := by
  have hfv (t : ℝ) : HasDerivAt (fun s ↦ f (R s x))
      (orbitDeriv R f (R t x)) t := by
    rw [orbitDeriv_flow R hR f t x]
    exact (hf x t).hasDerivAt
  have hva (t : ℝ) : HasDerivAt (fun s ↦ orbitDeriv R f (R s x))
      (orbitDeriv R (orbitDeriv R f) (R t x)) t := by
    rw [orbitDeriv_flow R hR (orbitDeriv R f) t x]
    exact (hv x t).hasDerivAt
  have hfree := planarQuadraticLift_free hfv hva (fun t ↦ hunit (R t x)) 0
  have hsecond : (fun t ↦ orbitDeriv R (fun y ↦ planarQuadraticLift (f y)) (R t x)) =
      deriv (fun t ↦ planarQuadraticLift (f (R t x))) := by
    funext t
    exact orbitDeriv_flow R hR (fun y ↦ planarQuadraticLift (f y)) t x
  change LinearIndependent ℝ ![deriv (fun t ↦ planarQuadraticLift (f (R t x))) 0,
    deriv (fun t ↦ orbitDeriv R (fun y ↦ planarQuadraticLift (f y)) (R t x)) 0]
  rw [hsecond]
  exact hfree

/-- The actual lift has genuinely nonzero orbit speed, providing the input to
the genuine intrinsic speed normalization in dimension three. -/
theorem planarQuadraticLift_orbitDeriv_ne_zero {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (f : M → Planar) (hf : ∀ x, Differentiable ℝ (fun t ↦ f (R t x)))
    (hv : ∀ x, Differentiable ℝ (fun t ↦ orbitDeriv R f (R t x)))
    (hunit : ∀ x, ‖orbitDeriv R f x‖ = 1) (x : M) :
    orbitDeriv R (fun y ↦ planarQuadraticLift (f y)) x ≠ 0 := by
  simpa only [Matrix.cons_val_zero] using
    (planarQuadraticLift_orbit_free R hR f hf hv hunit x).ne_zero 0

/-- The actual two common orbit derivatives remain free under an actual
normalization's triangular derivative identities. The nonzero coefficients
are the genuine normalization scales, not an assumption of final freeness. -/
theorem actual_normalized_curve_free {M : Type*}
    (R : ℝ → M → M) (q c : M → SpaceCurve) (ψ : M → M)
    (α β μ : M → ℝ)
    (hq : ∀ x, LinearIndependent ℝ ![orbitDeriv R q x,
      orbitDeriv R (orbitDeriv R q) x])
    (hα : ∀ x, α x ≠ 0) (hβ : ∀ x, β x ≠ 0)
    (hfirst : ∀ x, orbitDeriv R c x = α x • orbitDeriv R q (ψ x))
    (hsecond : ∀ x, orbitDeriv R (orbitDeriv R c) x =
      β x • orbitDeriv R (orbitDeriv R q) (ψ x) + μ x • orbitDeriv R q (ψ x))
    (x : M) :
    LinearIndependent ℝ ![orbitDeriv R c x, orbitDeriv R (orbitDeriv R c) x] := by
  rw [hfirst, hsecond]
  exact free_jets_triangular (hq (ψ x)) (hα x) (hβ x) (μ x)

/-- Genuine twice differentiable changes of orbit time, with nonzero actual
time derivative, preserve the freedom of actual real curve derivatives. This
also includes the actual orbit-constant outer scale in speed normalization;
neither transformed jet identity is assumed. -/
theorem actual_reparametrized_profile_free
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q : ℝ → V) (hq : Differentiable ℝ q) (hdq : Differentiable ℝ (deriv q))
    (hfree : ∀ t, LinearIndependent ℝ ![deriv q t, deriv (deriv q) t])
    (τ : ℝ → ℝ) (hτ : Differentiable ℝ τ) (hdτ : Differentiable ℝ (deriv τ))
    {b : ℝ} (hb : b ≠ 0) {t : ℝ} (hτt : deriv τ t ≠ 0) :
    LinearIndependent ℝ ![deriv (fun s ↦ b • q (τ s)) t,
      deriv (deriv (fun s ↦ b • q (τ s))) t] := by
  have hfirst : deriv (fun s ↦ b • q (τ s)) =
      fun s ↦ b • (deriv τ s • deriv q (τ s)) := by
    funext s
    exact (((hq (τ s)).hasDerivAt.scomp s (hτ s).hasDerivAt).const_smul b).deriv
  have hsecond : deriv (deriv (fun s ↦ b • q (τ s))) t =
      (b * deriv τ t ^ 2) • deriv (deriv q) (τ t) +
        (b * deriv (deriv τ) t) • deriv q (τ t) := by
    rw [hfirst]
    have hd := (((hdτ t).hasDerivAt.smul
      ((hdq (τ t)).hasDerivAt.scomp t (hτ t).hasDerivAt)).const_smul b).deriv
    change deriv (fun s ↦ b • (deriv τ s • deriv q (τ s))) t = _ at hd
    simpa only [smul_add, smul_smul, pow_two, mul_assoc, add_comm,
      Pi.smul_apply, Function.comp_def] using hd
  rw [hsecond, hfirst]
  simpa only [smul_smul] using
    (free_jets_triangular (hfree (τ t)) (mul_ne_zero hb hτt)
      (mul_ne_zero hb (pow_ne_zero _ hτt)) (b * deriv (deriv τ) t))

/-- The literal orbit formula of an actual normalization transfers the freedom
of the original actual global curve. No transformed derivative is supplied:
both are differentiated from this actual formula. -/
theorem normalized_curve_free_of_orbit_formula {M : Type*}
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (q c : M → SpaceCurve)
    (hq : ∀ x, Differentiable ℝ (fun t ↦ q (R t x)))
    (hdq : ∀ x, Differentiable ℝ (fun t ↦ orbitDeriv R q (R t x)))
    (hfree : ∀ x, LinearIndependent ℝ ![orbitDeriv R q x,
      orbitDeriv R (orbitDeriv R q) x])
    (τ : M → ℝ → ℝ) (hτ : ∀ x, Differentiable ℝ (τ x))
    (hdτ : ∀ x, Differentiable ℝ (deriv (τ x)))
    (htime : ∀ x, deriv (τ x) 0 ≠ 0)
    (b : M → ℝ) (hb : ∀ x, b x ≠ 0)
    (hformula : ∀ x t, c (R t x) = b x • q (R (τ x t) x)) (x : M) :
    LinearIndependent ℝ ![orbitDeriv R c x, orbitDeriv R (orbitDeriv R c) x] := by
  have hqprime : (fun t ↦ orbitDeriv R q (R t x)) =
      deriv (fun t ↦ q (R t x)) := by
    funext t
    exact orbitDeriv_flow R hR q t x
  have hdq' : Differentiable ℝ (deriv (fun t ↦ q (R t x))) := by
    rw [← hqprime]
    exact hdq x
  have hqfree (t : ℝ) : LinearIndependent ℝ ![deriv (fun s ↦ q (R s x)) t,
      deriv (deriv (fun s ↦ q (R s x))) t] := by
    have h := hfree (R t x)
    rw [orbitDeriv_flow R hR q t x,
      orbitDeriv_flow R hR (orbitDeriv R q) t x, hqprime] at h
    exact h
  have hf := actual_reparametrized_profile_free (fun t ↦ q (R t x))
    (hq x) hdq' hqfree (τ x) (hτ x) (hdτ x) (hb x) (htime x)
  have hcformula : (fun t ↦ c (R t x)) =
      fun t ↦ b x • q (R (τ x t) x) := funext (hformula x)
  change LinearIndependent ℝ ![deriv (fun t ↦ b x • q (R (τ x t) x)) 0,
    deriv (deriv (fun t ↦ b x • q (R (τ x t) x))) 0] at hf
  rw [← hcformula] at hf
  have hcprime : (fun t ↦ orbitDeriv R c (R t x)) =
      deriv (fun t ↦ c (R t x)) := by
    funext t
    exact orbitDeriv_flow R hR c t x
  change LinearIndependent ℝ ![deriv (fun t ↦ c (R t x)) 0,
    deriv (fun t ↦ orbitDeriv R c (R t x)) 0]
  rw [hcprime]
  exact hf

section Native
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- All genuine orbit-regularity inputs to the global free lift follow from
the actual jointly native smooth flow and actual native smooth planar map. -/
theorem planarQuadraticLift_native_free (R : PeriodOneSmoothFlow I M)
    (f : M → Planar) (hf : ContMDiff I 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ x, ‖orbitDeriv R.flow f x‖ = 1) (x : M) :
    LinearIndependent ℝ ![orbitDeriv R.flow (fun y ↦ planarQuadraticLift (f y)) x,
      orbitDeriv R.flow (orbitDeriv R.flow (fun y ↦ planarQuadraticLift (f y))) x] := by
  have hv := contMDiff_orbitDeriv R.flow R.smooth f hf
  exact planarQuadraticLift_orbit_free R.flow R.flow_add f
    (fun y t ↦ (hasDerivAt_orbit R.flow R.smooth R.flow_add f hf t y).differentiableAt)
    (fun y t ↦ (hasDerivAt_orbit R.flow R.smooth R.flow_add
      (orbitDeriv R.flow f) hv t y).differentiableAt) hunit x

/-- An actually normalized native smooth curve, with its genuine inverse-time
orbit formula, is free and has a constructed global native smooth unit binormal.
All actual derivative regularity is proved from native smoothness here. -/
theorem normalized_curve_free_binormal_of_orbit_formula
    (R : PeriodOneSmoothFlow I M) (q c : M → SpaceCurve)
    (hq : ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ q)
    (hc : ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ c)
    (hfree : ∀ x, LinearIndependent ℝ ![orbitDeriv R.flow q x,
      orbitDeriv R.flow (orbitDeriv R.flow q) x])
    (τ : M → ℝ → ℝ) (hτ : ∀ x, Differentiable ℝ (τ x))
    (hdτ : ∀ x, Differentiable ℝ (deriv (τ x)))
    (htime : ∀ x, deriv (τ x) 0 ≠ 0)
    (b : M → ℝ) (hb : ∀ x, b x ≠ 0)
    (hformula : ∀ x t, c (R.flow t x) = b x • q (R.flow (τ x t) x)) :
    (∀ x, LinearIndependent ℝ ![orbitDeriv R.flow c x,
      orbitDeriv R.flow (orbitDeriv R.flow c) x]) ∧
      ∃ ν : M → SpaceCurve, ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ ν ∧
        ∀ x, ‖ν x‖ = 1 ∧ ⟪ν x, orbitDeriv R.flow c x⟫_ℝ = 0 ∧
          ⟪ν x, orbitDeriv R.flow (orbitDeriv R.flow c) x⟫_ℝ = 0 := by
  have hqv := contMDiff_orbitDeriv R.flow R.smooth q hq
  have hcfree (x : M) := normalized_curve_free_of_orbit_formula R.flow R.flow_add q c
    (fun y t ↦ (hasDerivAt_orbit R.flow R.smooth R.flow_add q hq t y).differentiableAt)
    (fun y t ↦ (hasDerivAt_orbit R.flow R.smooth R.flow_add
      (orbitDeriv R.flow q) hqv t y).differentiableAt)
    hfree τ hτ hdτ htime b hb hformula x
  have hcv := contMDiff_orbitDeriv R.flow R.smooth c hc
  have hca := contMDiff_orbitDeriv R.flow R.smooth (orbitDeriv R.flow c) hcv
  refine ⟨hcfree, ⟨fun x ↦ spaceCurveUnitBinormal (orbitDeriv R.flow c x)
    (orbitDeriv R.flow (orbitDeriv R.flow c) x),
      spaceCurveUnitBinormal_contMDiff hcv hca hcfree, ?_⟩⟩
  exact fun x ↦ spaceCurveUnitBinormal_spec (hcfree x)

end Native

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.planarQuadraticLift_orbit_free
#print axioms GlobalEmbedding.Paper.planarQuadraticLift_orbitDeriv_ne_zero
#print axioms GlobalEmbedding.Paper.actual_normalized_curve_free
#print axioms GlobalEmbedding.Paper.actual_reparametrized_profile_free
#print axioms GlobalEmbedding.Paper.normalized_curve_free_of_orbit_formula
#print axioms GlobalEmbedding.Paper.planarQuadraticLift_native_free
#print axioms GlobalEmbedding.Paper.normalized_curve_free_binormal_of_orbit_formula
