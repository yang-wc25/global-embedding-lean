import GlobalEmbedding.Paper.PlanarOrbitNormalizationData
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import GlobalEmbedding.Paper.PlanarAnalyticCalculus
import GlobalEmbedding.Paper.PlanarNativeOrbitShiftInverse
import GlobalEmbedding.Paper.PlanarReflectionAreaZero
import GlobalEmbedding.Paper.PlanarHopfFourierReflection
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import GlobalEmbedding.External.SphereEversion.ToMathlib.Analysis.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Actual intrinsic orbit speed normalization

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, line261.
The normalized map uses the genuine speed integral and the genuine constructed inverse.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace GlobalEmbedding.Paper

variable {Q E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual real time isomorphism of the normalization lift on one orbit. -/
def planarOrbitNormalizationTimeIso (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : Q) : ℝ ≃o ℝ := by
  have hd (y : Q) : Differentiable ℝ
      (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) y) :=
    fun s ↦ (planarOrbitNormalizationLift_hasDerivAt R hadd hone g hn y (hc y) s).differentiableAt
  exact planarOrbitShiftLiftIso R (planarOrbitNormalizationShift R g)
    (planarOrbitShiftLift_strictMono R _
      (fun y s ↦ planarOrbitNormalizationLift_deriv_pos R hadd hone g hn y (hc y) s))
    (planarOrbitShiftLift_surjective R hadd hone _ (fun y ↦ (hd y).continuous)) z

/-- The genuine normalized map displayed in the source. -/
def planarOrbitReparametrized (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : Q) : E :=
  (planarOrbitLength R g z)⁻¹ •
    g ((planarOrbitNormalizationEquiv R hzero hadd hone g hn hc).symm z)

/-- The true inverse on an entire orbit uses the actual scalar time inverse. -/
theorem planarOrbitNormalizationEquiv_symm_orbit (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : Q) (s : ℝ) :
    (planarOrbitNormalizationEquiv R hzero hadd hone g hn hc).symm (R s z) =
      R ((planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm s) z := by
  exact planarOrbitShiftEquiv_symm_orbit R hzero hadd _ _ _ z s

/-- The literal whole-orbit formula used by the free-curve assembly. -/
theorem planarOrbitReparametrized_orbit (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : Q) (s : ℝ) :
    planarOrbitReparametrized R hzero hadd hone g hn hc (R s z) =
      (planarOrbitLength R g z)⁻¹ •
        g (R ((planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm s) z) := by
  rw [planarOrbitReparametrized, planarOrbitLength_flow R hadd hone,
    planarOrbitNormalizationEquiv_symm_orbit R hzero hadd hone]

/-- The actual scalar inverse derivative is the reciprocal genuine speed ratio. -/
theorem planarOrbitNormalizationTimeIso_symm_hasDerivAt (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : Q) (s : ℝ) :
    HasDerivAt (planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm
      (planarOrbitSpeed R g
        (R ((planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm s) z) /
          planarOrbitLength R g z)⁻¹ s := by
  let e := planarOrbitNormalizationTimeIso R hadd hone g hn hc z
  have hd := planarOrbitNormalizationLift_hasDerivAt R hadd hone g hn z (hc z) (e.symm s)
  have hp : planarOrbitSpeed R g (R (e.symm s) z) / planarOrbitLength R g z ≠ 0 :=
    ne_of_gt (div_pos (norm_pos_iff.mpr (hn _)) (planarOrbitLength_pos R g hn z (hc z)))
  exact HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt hd hp
    (Filter.Eventually.of_forall fun y ↦ e.apply_symm_apply y)

/-- The true normalized whole-orbit map has derivative the original derivative
at the actual inverse point divided by its own genuine speed. -/
theorem planarOrbitReparametrized_hasDerivAt (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : Q) (s : ℝ) :
    HasDerivAt (fun t ↦ planarOrbitReparametrized R hzero hadd hone g hn hc (R t z))
      ((planarOrbitSpeed R g
        (R ((planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm s) z))⁻¹ •
        orbitDeriv R g
          (R ((planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm s) z)) s := by
  let e := planarOrbitNormalizationTimeIso R hadd hone g hn hc z
  have heq : (fun t ↦ planarOrbitReparametrized R hzero hadd hone g hn hc (R t z)) =
      fun t ↦ (planarOrbitLength R g z)⁻¹ • g (R (e.symm t) z) := by
    funext t
    rw [planarOrbitReparametrized, planarOrbitLength_flow R hadd hone,
      planarOrbitNormalizationEquiv_symm_orbit R hzero hadd hone]
  have hn' : deriv (fun t : ℝ ↦ g (R t z)) (e.symm s) ≠ 0 := by
    rw [← orbitDeriv_flow R hadd g (e.symm s) z]
    exact hn _
  have hg := (differentiableAt_of_deriv_ne_zero hn').hasDerivAt
  rw [← orbitDeriv_flow R hadd g (e.symm s) z] at hg
  have hi := planarOrbitNormalizationTimeIso_symm_hasDerivAt R hadd hone g hn hc z s
  have hd := (hg.scomp s hi).const_smul (planarOrbitLength R g z)⁻¹
  simp only [Function.comp_def, smul_smul] at hd
  have hL : planarOrbitLength R g z ≠ 0 := ne_of_gt (planarOrbitLength_pos R g hn z (hc z))
  have hcancel : (planarOrbitLength R g z)⁻¹ *
      (planarOrbitSpeed R g (R (e.symm s) z) / planarOrbitLength R g z)⁻¹ =
        (planarOrbitSpeed R g (R (e.symm s) z))⁻¹ := by
    rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hL, one_mul]
  rw [hcancel] at hd
  rw [heq]
  exact hd

/-- Actual unit speed for the literal normalized map, with respect to the
same original orbit derivative used to construct it. -/
theorem planarOrbitReparametrized_unitSpeed (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : Q) :
    ‖orbitDeriv R (planarOrbitReparametrized R hzero hadd hone g hn hc) z‖ = 1 := by
  unfold orbitDeriv
  rw [(planarOrbitReparametrized_hasDerivAt R hzero hadd hone g hn hc z 0).deriv]
  let y := R ((planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm 0) z
  have ha : 0 < planarOrbitSpeed R g y := norm_pos_iff.mpr (hn y)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
  change (planarOrbitSpeed R g y)⁻¹ * planarOrbitSpeed R g y = 1
  exact inv_mul_cancel₀ ha.ne'

/-- The literal normalized map inherits the actual half-period reflection. -/
theorem planarOrbitReparametrized_half (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → E) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)))
    (A : E ≃ₗᵢ[ℝ] E) (ha : ∀ z, g (R (1 / 2 : ℝ) z) = A (g z)) (z : Q) :
    planarOrbitReparametrized R hzero hadd hone g hn hc (R (1 / 2 : ℝ) z) =
      A (planarOrbitReparametrized R hzero hadd hone g hn hc z) := by
  have hi : (planarOrbitNormalizationEquiv R hzero hadd hone g hn hc).symm
      (R (1 / 2 : ℝ) z) = R (1 / 2 : ℝ)
        ((planarOrbitNormalizationEquiv R hzero hadd hone g hn hc).symm z) :=
    planarOrbitShiftEquiv_symm_half R hzero hadd _ _ _
      (planarOrbitNormalizationShift_half R hadd g hn A ha) z
  unfold planarOrbitReparametrized
  rw [planarOrbitLength_half R hadd g hn A ha, hi, ha, map_smul]

/-- The actual normalized planar observable has the original zero signed area,
as a consequence of its actual inherited reflection. -/
theorem planarOrbitReparametrized_signedArea (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → Planar) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)))
    (ha : ∀ z, g (R (1 / 2 : ℝ) z) = planarReflection (g z)) (z : Q) :
    let f := planarOrbitReparametrized R hzero hadd hone g hn hc
    orbitAverage R (fun y ↦ f y 0 * orbitDeriv R f y 1 -
      f y 1 * orbitDeriv R f y 0) z = 0 := by
  exact planar_reflection_signed_area_zero R hzero hadd hone _
    (fun y t ↦
      (planarOrbitReparametrized_hasDerivAt R hzero hadd hone g hn hc y t).differentiableAt)
    (planarOrbitReparametrized_half R hzero hadd hone g hn hc
      planarReflectionLinearIsometryEquiv ha) z

section Native

variable {P M F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [TopologicalSpace M] [ChartedSpace P M]
  [IsManifold 𝓘(ℝ, P) ∞ M] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [FiniteDimensional ℝ P] in
/-- The genuine nonvanishing orbit derivative has native smooth speed. -/
theorem planarOrbitSpeed_contMDiff (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → F)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (planarOrbitSpeed R g) := by
  have hd := contMDiff_orbitDeriv R hR g hg
  intro x
  exact (contDiffAt_norm ℝ (hn x)).comp_contMDiffAt (hd x)

/-- The actual speed period integral is native smooth, by the accepted
compact parameter integral theorem on the original native manifold. -/
theorem planarOrbitLength_contMDiff (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → F)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (planarOrbitLength R g) := by
  have hS := planarOrbitSpeed_contMDiff R hR g hg hn
  have hRs : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) ∞
      (fun p : M × ℝ ↦ R p.2 p.1) := hR.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hi := contMDiff_compact_parameter_integral (⊤ : ℕ∞)
    (fun p : M × ℝ ↦ planarOrbitSpeed R g (R p.2 p.1)) (hS.comp hRs)
  apply hi.congr
  intro z
  unfold planarOrbitLength orbitAverage
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The literal normalization primitive is native smooth; all its data are
constructed from the original smooth observable and genuine flow. -/
theorem planarOrbitNormalizationShift_contMDiff (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → F)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (planarOrbitNormalizationShift R g) := by
  have hS := planarOrbitSpeed_contMDiff R hR g hg hn
  have hL := planarOrbitLength_contMDiff R hR g hg hn
  have hLpos (z : M) : 0 < planarOrbitLength R g z := by
    apply planarOrbitLength_pos R g hn z
    exact (contMDiff_orbitDeriv R hR g hg).continuous.comp
      (hR.continuous.comp (continuous_id.prodMk continuous_const))
  have hU : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ (planarOrbitNormalizationDensity R g) := by
    exact (hS.mul (hL.inv₀ (fun z ↦ ne_of_gt (hLpos z)))).sub contMDiff_const
  exact planarOrbitPrimitive_contMDiff R
    (hR.comp (contMDiff_snd.prodMk contMDiff_fst)) _ hU

/-- The actual inverse time on every orbit is genuinely C∞. The accepted
parametric scalar inverse theorem is applied with a dummy real parameter;
all positivity and surjectivity properties come from the actual construction. -/
theorem planarOrbitNormalizationTimeIso_symm_contDiff (R : ℝ → M → M)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2))
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : M → F) (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g)
    (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) (z : M) :
    ContDiff ℝ ∞ (planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm := by
  have hH := planarOrbitNormalizationShift_contMDiff R hR g hg hn
  have hcurve : ContDiff ℝ ∞
      (fun t : ℝ ↦ planarOrbitNormalizationShift R g (R t z)) :=
    (hH.comp (hR.comp (contMDiff_id.prodMk contMDiff_const))).contDiff
  have hF : ContDiff ℝ ∞ (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) z) :=
    contDiff_id.add hcurve
  let f : ℝ → ℝ → ℝ := fun _ ↦ planarOrbitShiftLift R (planarOrbitNormalizationShift R g) z
  have hfs : ContDiff ℝ ∞ (Function.uncurry f) := hF.comp contDiff_snd
  have hfp : ∀ x t, 0 < partialDerivSnd f x t :=
    fun _ t ↦ planarOrbitNormalizationLift_deriv_pos R hadd hone g hn z (hc z) t
  have hd (y : M) : Differentiable ℝ
      (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) y) := fun t ↦
    (planarOrbitNormalizationLift_hasDerivAt R hadd hone g hn y (hc y) t).differentiableAt
  have hsurj : ∀ x, Function.Surjective (f x) := fun _ ↦
    planarOrbitShiftLift_surjective R hadd hone _ (fun y ↦ (hd y).continuous) z
  have hi := contDiff_parametric_symm_of_deriv_pos hfs hfp hsurj
  have hh := hi.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun t : ℝ ↦ ((0 : ℝ), t)))
  exact hh

/-- The actual normalization equivalence has a native smooth forward map. -/
theorem planarOrbitNormalizationEquiv_contMDiff (R : ℝ → M → M)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → F)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ (planarOrbitNormalizationEquiv R hzero hadd hone g hn hc) :=
  hR.comp ((planarOrbitNormalizationShift_contMDiff R hR g hg hn).prodMk contMDiff_id)

/-- Native smoothness of the same genuine global inverse, by the accepted
open-chart scalar-root theorem and W5's native global inverse bridge. -/
theorem planarOrbitNormalizationEquiv_symm_contMDiff (R : ℝ → M → M)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → F)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) ∞
      (planarOrbitNormalizationEquiv R hzero hadd hone g hn hc).symm := by
  have hd (z : M) : Differentiable ℝ
      (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) z) := fun t ↦
    (planarOrbitNormalizationLift_hasDerivAt R hadd hone g hn z (hc z) t).differentiableAt
  exact planarPositiveOrbitShiftEquiv_symm_contMDiff R hzero hadd hone hR _
    (planarOrbitNormalizationShift_contMDiff R hR g hg hn)
    (fun z ↦ (hd z).continuous)
    (fun z t ↦ planarOrbitNormalizationLift_deriv_pos R hadd hone g hn z (hc z) t)

/-- The literal normalized observable is native smooth, with all speed,
length, shift and inverse data constructed from the original input. -/
theorem planarOrbitReparametrized_contMDiff (R : ℝ → M → M)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → F)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z))) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞
      (planarOrbitReparametrized R hzero hadd hone g hn hc) := by
  have hL := planarOrbitLength_contMDiff R hR g hg hn
  exact (hL.inv₀ (fun z ↦ ne_of_gt (planarOrbitLength_pos R g hn z (hc z)))).smul
    (hg.comp (planarOrbitNormalizationEquiv_symm_contMDiff R hzero hadd hone hR g hg hn hc))

end Native

section Analytic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The genuine nonzero speed is analytic on every original orbit. -/
theorem planarOrbitSpeed_orbit_analytic (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (g : Q → F)
    (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (ha : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (R t z)) Set.univ) (z : Q) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ planarOrbitSpeed R g (R t z)) Set.univ := by
  intro t _
  have hv := (ha z).deriv t (Set.mem_univ t)
  have hn' : deriv (fun s : ℝ ↦ g (R s z)) t ≠ 0 := by
    rw [← orbitDeriv_flow R hadd g t z]
    exact hn _
  have hh := planar_analyticAt_norm_curve hv hn'
  simpa only [planarOrbitSpeed, orbitDeriv_flow R hadd] using hh

/-- Actual orbit invariance of L makes the genuine density orbit analytic. -/
theorem planarOrbitNormalizationDensity_orbit_analytic (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → F) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)))
    (ha : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (R t z)) Set.univ) (z : Q) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ planarOrbitNormalizationDensity R g (R t z)) Set.univ := by
  have he : (fun t : ℝ ↦ planarOrbitNormalizationDensity R g (R t z)) =
      fun t : ℝ ↦ planarOrbitSpeed R g (R t z) / planarOrbitLength R g z - 1 := by
    funext t
    rw [planarOrbitNormalizationDensity, planarOrbitLength_flow R hadd hone]
  rw [he]
  intro t _
  exact ((planarOrbitSpeed_orbit_analytic R hadd g hn ha z t (Set.mem_univ t)).div
    analyticAt_const (ne_of_gt (planarOrbitLength_pos R g hn z (hc z)))).sub analyticAt_const

/-- The actual normalization shift, rather than a chosen analytic replacement,
is analytic along each original orbit. -/
theorem planarOrbitNormalizationShift_orbit_analytic (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → F) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)))
    (ha : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (R t z)) Set.univ) (z : Q) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ planarOrbitNormalizationShift R g (R t z)) Set.univ :=
  planarOrbitPrimitive_orbit_analytic R hadd hone _ z
    (planarOrbitNormalizationDensity_orbit_analytic R hadd hone g hn hc ha z)

/-- The actual positive time inverse is analytic along every orbit. -/
theorem planarOrbitNormalizationTimeIso_symm_analytic (R : ℝ → Q → Q)
    (hadd : ∀ s t z, R (s + t) z = R s (R t z)) (hone : ∀ z, R 1 z = z)
    (g : Q → F) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)))
    (ha : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (R t z)) Set.univ) (z : Q) :
    AnalyticOnNhd ℝ (planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm Set.univ := by
  intro s _
  let e := planarOrbitNormalizationTimeIso R hadd hone g hn hc z
  have hF : AnalyticAt ℝ (planarOrbitShiftLift R (planarOrbitNormalizationShift R g) z)
      (e.symm s) := analyticAt_id.add
    (planarOrbitNormalizationShift_orbit_analytic R hadd hone g hn hc ha z (e.symm s)
      (Set.mem_univ _))
  exact planarOrbitShiftLiftIso_symm_analyticAt R _ _ _ z s hF
    (ne_of_gt (planarOrbitNormalizationLift_deriv_pos R hadd hone g hn z (hc z) (e.symm s)))

/-- The literal normalized map is analytic on each entire original orbit. -/
theorem planarOrbitReparametrized_orbit_analytic (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z) (g : Q → F) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)))
    (ha : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (R t z)) Set.univ) (z : Q) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦
      planarOrbitReparametrized R hzero hadd hone g hn hc (R t z)) Set.univ := by
  have he : (fun t : ℝ ↦ planarOrbitReparametrized R hzero hadd hone g hn hc (R t z)) =
      fun t : ℝ ↦ (planarOrbitLength R g z)⁻¹ •
        g (R ((planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm t) z) := by
    funext t
    exact planarOrbitReparametrized_orbit R hzero hadd hone g hn hc z t
  rw [he]
  intro t _
  have hi := planarOrbitNormalizationTimeIso_symm_analytic R hadd hone g hn hc ha z t
    (Set.mem_univ t)
  have hg := (ha z _ (Set.mem_univ _)).comp
    (f := (planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm) hi
  exact analyticAt_const.smul hg

end Analytic

section CompleteNormalization

variable {P M F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [TopologicalSpace M] [ChartedSpace P M]
  [IsManifold 𝓘(ℝ, P) ∞ M] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

/-- The full intrinsic reparametrization proposition: the actual positive
length and literal weighted primitive construct a genuine smooth orbit-preserving
equivalence with smooth inverse, and its literal normalized map is smooth with
unit actual orbit speed. Reflection and orbit analyticity pass to this same map.
All orbit continuity used by the construction follows from the original native
smooth data; no desired inverse, normalized map or derivative regularity is supplied. -/
theorem planar_orbit_reparametrize (R : ℝ → M → M)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → F)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0) :
    ∃ hc : ∀ z, Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)),
      let Φ := planarOrbitNormalizationEquiv R hzero hadd hone g hn hc
      let f := planarOrbitReparametrized R hzero hadd hone g hn hc
      ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ Φ ∧
      ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) ∞ Φ.symm ∧
      (∀ z, Φ z = R (planarOrbitNormalizationShift R g z) z) ∧
      (∀ z, ∃ t : ℝ, Φ.symm z = R t z) ∧
      (∀ z, 0 < planarOrbitLength R g z) ∧
      (∀ z s, planarOrbitLength R g (R s z) = planarOrbitLength R g z) ∧
      ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ f ∧
      (∀ z, ‖orbitDeriv R f z‖ = 1) ∧
      (∀ A : F ≃ₗᵢ[ℝ] F, (∀ z, g (R (1 / 2 : ℝ) z) = A (g z)) →
        ∀ z, f (R (1 / 2 : ℝ) z) = A (f z)) ∧
      ((∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (R t z)) Set.univ) →
        ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (R t z)) Set.univ) := by
  have hc (z : M) : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)) :=
    (contMDiff_orbitDeriv R hR g hg).continuous.comp
      (hR.continuous.comp (continuous_id.prodMk continuous_const))
  refine ⟨hc, planarOrbitNormalizationEquiv_contMDiff R hzero hadd hone hR g hg hn hc,
    planarOrbitNormalizationEquiv_symm_contMDiff R hzero hadd hone hR g hg hn hc,
    (fun _ ↦ rfl), ?_, (fun z ↦ planarOrbitLength_pos R g hn z (hc z)),
    (fun z s ↦ planarOrbitLength_flow R hadd hone g z s),
    planarOrbitReparametrized_contMDiff R hzero hadd hone hR g hg hn hc,
    planarOrbitReparametrized_unitSpeed R hzero hadd hone g hn hc,
    (fun A hA ↦ planarOrbitReparametrized_half R hzero hadd hone g hn hc A hA),
    (fun ha ↦ planarOrbitReparametrized_orbit_analytic R hzero hadd hone g hn hc ha)⟩
  intro z
  exact ⟨(planarOrbitNormalizationTimeIso R hadd hone g hn hc z).symm 0,
    by simpa only [hzero] using
      planarOrbitNormalizationEquiv_symm_orbit R hzero hadd hone g hn hc z 0⟩

end CompleteNormalization

section PlanarNormalization

variable {P M : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [TopologicalSpace M] [ChartedSpace P M]
  [IsManifold 𝓘(ℝ, P) ∞ M]

/-- From the genuine smooth reflected orbit-analytic immersion, construct one
actual map satisfying all normalization clauses, including the original signed area.
This is the normalization step only: the original source immersion is still constructed
by the independent initial-map and Fourier steps of the full planar target. -/
theorem planar_orbit_unit_reflected_analytic (R : ℝ → M → M)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (hone : ∀ z, R 1 z = z)
    (hR : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞
      (fun p : ℝ × M ↦ R p.1 p.2)) (g : M → Planar)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, Planar) ∞ g) (hn : ∀ z, orbitDeriv R g z ≠ 0)
    (ha : ∀ z, g (R (1 / 2 : ℝ) z) = planarReflection (g z))
    (han : ∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ g (R t z)) Set.univ) :
    ∃ f : M → Planar, ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, Planar) ∞ f ∧
      (∀ z, ‖orbitDeriv R f z‖ = 1) ∧
      (∀ z, f (R (1 / 2 : ℝ) z) = planarReflection (f z)) ∧
      (∀ z, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (R t z)) Set.univ) ∧
      (∀ z, orbitAverage R (fun y ↦ f y 0 * orbitDeriv R f y 1 -
        f y 1 * orbitDeriv R f y 0) z = 0) := by
  have hc (z : M) : Continuous (fun t : ℝ ↦ orbitDeriv R g (R t z)) :=
    (contMDiff_orbitDeriv R hR g hg).continuous.comp
      (hR.continuous.comp (continuous_id.prodMk continuous_const))
  refine ⟨planarOrbitReparametrized R hzero hadd hone g hn hc,
    planarOrbitReparametrized_contMDiff R hzero hadd hone hR g hg hn hc,
    planarOrbitReparametrized_unitSpeed R hzero hadd hone g hn hc,
    planarOrbitReparametrized_half R hzero hadd hone g hn hc
      planarReflectionLinearIsometryEquiv ha,
    planarOrbitReparametrized_orbit_analytic R hzero hadd hone g hn hc han,
    planarOrbitReparametrized_signedArea R hzero hadd hone g hn hc ha⟩

end PlanarNormalization

#print axioms planar_orbit_unit_reflected_analytic
#print axioms planarOrbitReparametrized_signedArea
#print axioms planar_orbit_reparametrize
#print axioms planarOrbitReparametrized_orbit_analytic
#print axioms planarOrbitReparametrized_contMDiff

#print axioms planarOrbitNormalizationTimeIso_symm_contDiff
#print axioms planarOrbitReparametrized_half
#print axioms planarOrbitNormalizationShift_contMDiff
#print axioms planarOrbitReparametrized_hasDerivAt
#print axioms planarOrbitReparametrized_unitSpeed

end GlobalEmbedding.Paper
