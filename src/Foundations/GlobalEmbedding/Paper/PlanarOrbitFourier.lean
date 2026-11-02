import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import GlobalEmbedding.Paper.PlanarFourierKernelApproximation
import GlobalEmbedding.Paper.PlanarFourierOrbitAnalytic
import GlobalEmbedding.Paper.MatrixManifoldCompactParameterIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Finite Fourier approximation on actual period-one orbits

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:planar`,
proof line 262. Exclusive W1 node: `planar-orbit-fourier`.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The genuine quotient of a continuous period-one map. Its values at real representatives
are exactly the original values, so no choice of a fundamental interval changes the map. -/
def planarPeriodicContinuousMap {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (hf : Function.Periodic f 1) : C(AddCircle (1 : ℝ), E) :=
  ⟨hf.lift, isQuotientMap_quotient_mk'.continuous_iff.mpr f.continuous⟩

@[simp] theorem planarPeriodicContinuousMap_coe {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (hf : Function.Periodic f 1) (t : ℝ) :
    planarPeriodicContinuousMap f hf (t : AddCircle (1 : ℝ)) = f t := rfl

/-- The actual orbit family as a continuous map with values in continuous maps. -/
def planarContinuousOrbit {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2)) :
    C(AddCircle (1 : ℝ), C(M, E)) :=
  planarPeriodicContinuousMap (ContinuousMap.curry ⟨_, g.continuous.comp hc⟩)
    (by intro t; ext x; exact orbitMap_periodic R hR h1 g x t)

@[simp] theorem planarContinuousOrbit_coe {M E : Type*}
    [TopologicalSpace M] [TopologicalSpace E]
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2)) (t : ℝ) (x : M) :
    planarContinuousOrbit R hR h1 g hc (t : AddCircle (1 : ℝ)) x = g (R t x) := rfl

/-- Translation in the quotient is exactly translation along the original flow. -/
theorem planarContinuousOrbit_flow {M E : Type*}
    [TopologicalSpace M] [TopologicalSpace E]
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (θ : AddCircle (1 : ℝ)) (s : ℝ) (x : M) :
    planarContinuousOrbit R hR h1 g hc θ (R s x) =
      planarContinuousOrbit R hR h1 g hc (θ + (s : AddCircle (1 : ℝ))) x := by
  induction θ using Quotient.inductionOn' with | h t =>
    change g (R t (R s x)) = g (R (t + s) x)
    rw [hR]

section Convolution

variable {M E : Type*} [TopologicalSpace M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual continuous Fourier convolution. The same scalar kernel is used at every
point of the compact parameter manifold. -/
def planarOrbitConvolution
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (p : C(AddCircle (1 : ℝ), ℂ)) : C(M, E) :=
  ∫ θ, (p θ).re • planarContinuousOrbit R hR h1 g hc θ ∂AddCircle.haarAddCircle

/-- Evaluation commutes with the genuine Banach-valued integral. -/
theorem planarOrbitConvolution_apply
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (p : C(AddCircle (1 : ℝ), ℂ)) (x : M) :
    planarOrbitConvolution R hR h1 g hc p x =
      ∫ θ, (p θ).re • planarContinuousOrbit R hR h1 g hc θ x
        ∂AddCircle.haarAddCircle := by
  apply ContinuousMap.integral_apply
  exact ((Complex.continuous_re.comp p.continuous).smul
    (planarContinuousOrbit R hR h1 g hc).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Haar translation moves the actual orbit translation onto the scalar kernel.
Consequently a finite kernel yields a finite Fourier orbit, rather than a merely
pointwise approximation by unrelated analytic functions. -/
theorem planarOrbitConvolution_flow
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (p : C(AddCircle (1 : ℝ), ℂ)) (s : ℝ) (x : M) :
    planarOrbitConvolution R hR h1 g hc p (R s x) =
      ∫ θ, (p (θ - (s : AddCircle (1 : ℝ)))).re •
        planarContinuousOrbit R hR h1 g hc θ x ∂AddCircle.haarAddCircle := by
  rw [planarOrbitConvolution_apply]
  simp_rw [planarContinuousOrbit_flow]
  have ht := integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun θ : AddCircle (1 : ℝ) ↦ (p (θ - (s : AddCircle (1 : ℝ)))).re •
      planarContinuousOrbit R hR h1 g hc θ x) (s : AddCircle (1 : ℝ))
  simpa only [add_sub_cancel_right] using ht

/-- A single constructed finite Fourier kernel approximates an entire compact orbit family
in its uniform norm, including an empty parameter space. -/
theorem planar_orbit_uniform_fourier_approximation
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h0 : ∀ x, R 0 x = x) (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : C(AddCircle (1 : ℝ), ℂ),
      p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ)))) ∧
      ‖planarOrbitConvolution R hR h1 g hc p - g‖ < ε := by
  obtain ⟨p, hp, hclose⟩ := planar_fourier_kernel_approximation
    (planarContinuousOrbit R hR h1 g hc) ε hε
  have hz : planarContinuousOrbit R hR h1 g hc 0 = g := by
    ext x
    change g (R 0 x) = g x
    rw [h0]
  exact ⟨p, hp, by simpa only [planarOrbitConvolution, hz] using hclose⟩

/-- The common kernel acts componentwise on paired observables. -/
theorem planarOrbitConvolution_pair
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g h : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (p : C(AddCircle (1 : ℝ), ℂ)) (x : M) :
    planarOrbitConvolution R hR h1 (g.prodMk h) hc p x =
      (planarOrbitConvolution R hR h1 g hc p x,
        planarOrbitConvolution R hR h1 h hc p x) := by
  simp only [planarOrbitConvolution_apply]
  have heq (θ : AddCircle (1 : ℝ)) :
      (p θ).re • planarContinuousOrbit R hR h1 (g.prodMk h) hc θ x =
        ((p θ).re • planarContinuousOrbit R hR h1 g hc θ x,
          (p θ).re • planarContinuousOrbit R hR h1 h hc θ x) := by
    induction θ using Quotient.inductionOn' with | h t => rfl
  simp_rw [heq]
  apply integral_pair
  all_goals
    exact ((Complex.continuous_re.comp p.continuous).smul
      ((continuous_eval_const x).comp
        (planarContinuousOrbit R hR h1 _ hc).continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

/-- The same finite Fourier kernel simultaneously approximates two continuous observables
uniformly. Applied to `g` and its actual continuous orbit derivative this is the uniform
part of the C¹ approximation, once derivative commutation is established below. -/
theorem planar_orbit_pair_uniform_fourier_approximation
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h0 : ∀ x, R 0 x = x) (h1 : ∀ x, R 1 x = x) (g h : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : C(AddCircle (1 : ℝ), ℂ),
      p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ)))) ∧
      (∀ x, ‖planarOrbitConvolution R hR h1 g hc p x - g x‖ < ε) ∧
      (∀ x, ‖planarOrbitConvolution R hR h1 h hc p x - h x‖ < ε) := by
  obtain ⟨p, hp, hclose⟩ := planar_orbit_uniform_fourier_approximation
    R hR h0 h1 (g.prodMk h) hc ε hε
  have hpoint (x : M) :
      ‖(planarOrbitConvolution R hR h1 g hc p x - g x,
        planarOrbitConvolution R hR h1 h hc p x - h x)‖ < ε := by
    have heval := (ContinuousMap.norm_coe_le_norm
      (planarOrbitConvolution R hR h1 (g.prodMk h) hc p - g.prodMk h) x).trans_lt hclose
    rw [ContinuousMap.sub_apply, planarOrbitConvolution_pair] at heval
    exact heval
  exact ⟨p, hp, fun x ↦ (norm_fst_le _).trans_lt (hpoint x),
    fun x ↦ (norm_snd_le _).trans_lt (hpoint x)⟩

omit [CompactSpace M] [CompleteSpace E] in
/-- The continuous orbit integrand is genuinely Bochner integrable. -/
theorem planarOrbitWeightedIntegrable
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (p : C(AddCircle (1 : ℝ), ℂ)) (x : M) :
    Integrable (fun θ ↦ (p θ).re • planarContinuousOrbit R hR h1 g hc θ x)
      AddCircle.haarAddCircle :=
  ((Complex.continuous_re.comp p.continuous).smul
    ((continuous_eval_const x).comp
      (planarContinuousOrbit R hR h1 g hc).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Differentiation along the original flow commutes with convolution. The supplied
derivative data are the genuine one-variable derivatives, and compactness supplies the
uniform integrable dominator `‖p‖ * ‖dg‖`. This lemma is independent of Fourier truncation. -/
theorem planarOrbitConvolution_hasDerivAt
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g dg : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (hd : ∀ t x, HasDerivAt (fun s : ℝ ↦ g (R s x)) (dg (R t x)) t)
    (p : C(AddCircle (1 : ℝ), ℂ)) (s : ℝ) (x : M) :
    HasDerivAt (fun t : ℝ ↦ planarOrbitConvolution R hR h1 g hc p (R t x))
      (planarOrbitConvolution R hR h1 dg hc p (R s x)) s := by
  have hdiff (θ : AddCircle (1 : ℝ)) (t : ℝ) :
      HasDerivAt (fun u : ℝ ↦ (p θ).re •
        planarContinuousOrbit R hR h1 g hc θ (R u x))
        ((p θ).re • planarContinuousOrbit R hR h1 dg hc θ (R t x)) t := by
    apply HasDerivAt.const_smul
    induction θ using Quotient.inductionOn' with | h a =>
      simp only [planarContinuousOrbit_coe, ← hR]
      simpa only [Function.comp_def, one_smul] using
        (hd (a + t) x).scomp t ((hasDerivAt_id t).const_add a)
  have hbound (θ : AddCircle (1 : ℝ)) (t : ℝ) :
      ‖(p θ).re • planarContinuousOrbit R hR h1 dg hc θ (R t x)‖ ≤
        ‖p‖ * ‖dg‖ := by
    rw [norm_smul]
    apply mul_le_mul
    · calc
        ‖(p θ).re‖ = |(p θ).re| := Real.norm_eq_abs _
        _ ≤ ‖p θ‖ := Complex.abs_re_le_norm _
        _ ≤ ‖p‖ := ContinuousMap.norm_coe_le_norm p θ
    · induction θ using Quotient.inductionOn' with | h a =>
        exact ContinuousMap.norm_coe_le_norm dg (R a (R t x))
    · exact norm_nonneg _
    · exact norm_nonneg _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := AddCircle.haarAddCircle) (s := univ) (x₀ := s)
    (F := fun t θ ↦ (p θ).re • planarContinuousOrbit R hR h1 g hc θ (R t x))
    (F' := fun t θ ↦ (p θ).re • planarContinuousOrbit R hR h1 dg hc θ (R t x))
    (bound := fun _ ↦ ‖p‖ * ‖dg‖) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun t ↦
      (planarOrbitWeightedIntegrable R hR h1 g hc p (R t x)).aestronglyMeasurable)
    (planarOrbitWeightedIntegrable R hR h1 g hc p (R s x))
    (planarOrbitWeightedIntegrable R hR h1 dg hc p (R s x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ t _ ↦ hbound θ t)
    (integrable_const _) (Filter.Eventually.of_forall fun θ t _ ↦ hdiff θ t)
  simpa only [← planarOrbitConvolution_apply] using h.2

/-- The common orbit derivative is the actual convolution of the original derivative. -/
theorem orbitDeriv_planarOrbitConvolution
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h0 : ∀ x, R 0 x = x) (h1 : ∀ x, R 1 x = x) (g dg : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (hd : ∀ t x, HasDerivAt (fun s : ℝ ↦ g (R s x)) (dg (R t x)) t)
    (p : C(AddCircle (1 : ℝ), ℂ)) (x : M) :
    orbitDeriv R (planarOrbitConvolution R hR h1 g hc p) x =
      planarOrbitConvolution R hR h1 dg hc p x := by
  simpa only [orbitDeriv, h0] using
    (planarOrbitConvolution_hasDerivAt R hR h1 g dg hc hd p 0 x).deriv

/-- Every actual orbit of the finite convolution is real analytic on the whole real line.
The proof uses the proved Haar translation identity and the actual finite-kernel theorem. -/
theorem planarOrbitConvolution_orbit_analytic
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (p : C(AddCircle (1 : ℝ), ℂ))
    (hp : p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ))))) (x : M) :
    AnalyticOnNhd ℝ (fun t : ℝ ↦ planarOrbitConvolution R hR h1 g hc p (R t x))
      univ := by
  let F : C(AddCircle (1 : ℝ), E) :=
    ⟨fun θ ↦ planarContinuousOrbit R hR h1 g hc θ x,
      (continuous_eval_const x).comp (planarContinuousOrbit R hR h1 g hc).continuous⟩
  have ha := planar_fourier_translated_kernel_analytic F p hp
  change AnalyticOnNhd ℝ
    (fun s : ℝ ↦ ∫ θ, (p (θ - (s : AddCircle (1 : ℝ)))).re •
      planarContinuousOrbit R hR h1 g hc θ x ∂AddCircle.haarAddCircle) univ at ha
  simpa only [← planarOrbitConvolution_flow] using ha

/-- Convolution preserves the exact equivariance under a fixed linear map, at any chosen
time. No positivity, orthogonality or invertibility of that map is needed for this step. -/
theorem planarOrbitConvolution_equivariant
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (A : E →L[ℝ] E) (τ : ℝ) (hA : ∀ x, g (R τ x) = A (g x))
    (p : C(AddCircle (1 : ℝ), ℂ)) (x : M) :
    planarOrbitConvolution R hR h1 g hc p (R τ x) =
      A (planarOrbitConvolution R hR h1 g hc p x) := by
  rw [planarOrbitConvolution_apply, planarOrbitConvolution_apply,
    ← A.integral_comp_comm (planarOrbitWeightedIntegrable R hR h1 g hc p x)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  dsimp only
  rw [A.map_smul]
  congr 1
  induction θ using Quotient.inductionOn' with | h t =>
    change g (R t (R τ x)) = A (g (R t x))
    rw [← hR, add_comm t τ, hR, hA]

/-- The actual probability-Haar convolution equals the original length-one compact time
integral. There is no extra normalization or angular rescaling. -/
theorem planarOrbitConvolution_eq_setIntegral
    (R : ℝ → M → M) (hR : ∀ s t x, R (s + t) x = R s (R t x))
    (h1 : ∀ x, R 1 x = x) (g : C(M, E))
    (hc : Continuous (fun p : ℝ × M ↦ R p.1 p.2))
    (p : C(AddCircle (1 : ℝ), ℂ)) (x : M) :
    planarOrbitConvolution R hR h1 g hc p x =
      ∫ t in Icc (0 : ℝ) 1, (p (t : AddCircle (1 : ℝ))).re • g (R t x) := by
  rw [planarOrbitConvolution_apply, AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
  simp only [zero_add, planarContinuousOrbit_coe]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

end Convolution

universe u v w

/-- Genuine finite-kernel convolution preserves full native smoothness on a finite-dimensional
manifold without boundary. The compact parameter integral theorem includes true infinity. -/
theorem contMDiff_planarOrbitConvolution
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {M : Type v} [TopologicalSpace M] [ChartedSpace P M]
    [IsManifold 𝓘(ℝ, P) ∞ M] [CompactSpace M]
    {E : Type (max u w)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M) (g : C(M, E))
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ g)
    (p : C(AddCircle (1 : ℝ), ℂ))
    (hp : p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ))))) :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞
      (planarOrbitConvolution R.flow R.flow_add R.flow_one g R.smooth.continuous p) := by
  have hpSmooth : ContDiff ℝ ∞ (fun t : ℝ ↦ p (t : AddCircle (1 : ℝ))) := by
    apply AnalyticOnNhd.contDiff
    intro t _
    have ht : AnalyticAt ℝ (fun s : ℝ ↦ planarFourierKernelTranslate p (-s)) t :=
      (planar_fourier_kernel_translate_analytic p hp (-t)).comp
        (analyticAt_id.neg : AnalyticAt ℝ (fun s : ℝ ↦ -s) t)
    have heval := ((ContinuousMap.evalCLM ℝ (0 : AddCircle (1 : ℝ))).analyticAt
      (planarFourierKernelTranslate p (-t))).comp
        (f := fun s : ℝ ↦ planarFourierKernelTranslate p (-s)) (x := t) ht
    simpa [Function.comp_def, planarFourierKernelTranslate] using heval
  have hk : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ ↦ (p (t : AddCircle (1 : ℝ))).re) :=
    (Complex.reCLM.contDiff.comp hpSmooth).contMDiff
  have hF : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ ↦ (p (q.2 : AddCircle (1 : ℝ))).re • g (R.flow q.2 q.1)) :=
    (hk.comp contMDiff_snd).smul
      ((hg.comp R.smooth).comp (contMDiff_snd.prodMk contMDiff_fst))
  have hi := contMDiff_compact_parameter_integral (⊤ : ℕ∞) _ hF
  have heq : (fun x ↦ planarOrbitConvolution R.flow R.flow_add R.flow_one g
      R.smooth.continuous p x) =
      (fun x ↦ ∫ t in Icc (0 : ℝ) 1, (p (t : AddCircle (1 : ℝ))).re • g (R.flow t x)) := by
    funext x
    exact planarOrbitConvolution_eq_setIntegral _ _ _ _ _ _ _
  rwa [← heq] at hi

/-- Full smooth finite-kernel C¹ orbit approximation, with the original linear equivariance
and genuine real analyticity of every orbit. All approximation data are constructed.
The derivative is the common actual `orbitDeriv`, and one kernel works uniformly in `x`.
The finite Fourier span and the displayed convolution give the same finite orbit spectrum
at every parameter point, by `planarOrbitConvolution_flow`. -/
theorem planar_orbit_fourier_approximation
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {M : Type v} [TopologicalSpace M] [ChartedSpace P M]
    [IsManifold 𝓘(ℝ, P) ∞ M] [CompactSpace M]
    {E : Type (max u w)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M) (g : M → E)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ g)
    (A : E →L[ℝ] E) (τ : ℝ) (hA : ∀ x, g (R.flow τ x) = A (g x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : C(AddCircle (1 : ℝ), ℂ),
      p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ)))) ∧
      ∃ f : M → E,
        f = planarOrbitConvolution R.flow R.flow_add R.flow_one
          ⟨g, hg.continuous⟩ R.smooth.continuous p ∧
        ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ f ∧
        (∀ x, f (R.flow τ x) = A (f x)) ∧
        (∀ x, ‖f x - g x‖ < ε) ∧
        (∀ x, ‖orbitDeriv R.flow f x - orbitDeriv R.flow g x‖ < ε) ∧
        (∀ x, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (R.flow t x)) univ) := by
  let g₀ : C(M, E) := ⟨g, hg.continuous⟩
  let dg : C(M, E) := ⟨orbitDeriv R.flow g,
    (contMDiff_orbitDeriv R.flow R.smooth g hg).continuous⟩
  have hd : ∀ t x, HasDerivAt (fun s : ℝ ↦ g₀ (R.flow s x)) (dg (R.flow t x)) t :=
    hasDerivAt_orbit R.flow R.smooth R.flow_add g hg
  obtain ⟨p, hp, hval, hder⟩ := planar_orbit_pair_uniform_fourier_approximation
    R.flow R.flow_add R.flow_zero R.flow_one g₀ dg R.smooth.continuous ε hε
  refine ⟨p, hp, planarOrbitConvolution R.flow R.flow_add R.flow_one g₀
    R.smooth.continuous p, rfl, contMDiff_planarOrbitConvolution R g₀ hg p hp,
    planarOrbitConvolution_equivariant R.flow R.flow_add R.flow_one g₀
      R.smooth.continuous A τ hA p, hval, ?_, ?_⟩
  · intro x
    rw [orbitDeriv_planarOrbitConvolution R.flow R.flow_add R.flow_zero R.flow_one
      g₀ dg R.smooth.continuous hd]
    exact hder x
  · exact planarOrbitConvolution_orbit_analytic R.flow R.flow_add R.flow_one g₀
      R.smooth.continuous p hp

/-- A nowhere-zero continuous map on a compact space has a positive uniform norm margin.
The empty space is included explicitly. -/
theorem planar_compact_positive_norm_margin
    {M E : Type*} [TopologicalSpace M] [CompactSpace M] [NormedAddCommGroup E]
    (g : M → E) (hg : Continuous g) (hn : ∀ x, g x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ ‖g x‖ := by
  classical
  cases isEmpty_or_nonempty M with
  | inl h => exact ⟨1, zero_lt_one, fun x ↦ isEmptyElim x⟩
  | inr h =>
    obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hg.norm.continuousOn
    exact ⟨‖g x‖, norm_pos_iff.mpr (hn x), fun y ↦ hx (mem_univ y)⟩

/-- The full finite Fourier construction also preserves the nowhere-zero actual orbit
derivative. Choose the approximation tolerance below both the requested tolerance and half
the genuine positive compact norm margin. This uses no supplied margin or nonzero result. -/
theorem planar_orbit_fourier_nonvanishing
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {M : Type v} [TopologicalSpace M] [ChartedSpace P M]
    [IsManifold 𝓘(ℝ, P) ∞ M] [CompactSpace M]
    {E : Type (max u w)} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M) (g : M → E)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ g)
    (A : E →L[ℝ] E) (τ : ℝ) (hA : ∀ x, g (R.flow τ x) = A (g x))
    (hn : ∀ x, orbitDeriv R.flow g x ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : C(AddCircle (1 : ℝ), ℂ),
      p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ)))) ∧
      ∃ f : M → E,
        f = planarOrbitConvolution R.flow R.flow_add R.flow_one
          ⟨g, hg.continuous⟩ R.smooth.continuous p ∧
        ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, E) ∞ f ∧
        (∀ x, f (R.flow τ x) = A (f x)) ∧
        (∀ x, ‖f x - g x‖ < ε) ∧
        (∀ x, ‖orbitDeriv R.flow f x - orbitDeriv R.flow g x‖ < ε) ∧
        (∀ x, AnalyticOnNhd ℝ (fun t : ℝ ↦ f (R.flow t x)) univ) ∧
        (∀ x, orbitDeriv R.flow f x ≠ 0) := by
  obtain ⟨δ, hδ, hmargin⟩ := planar_compact_positive_norm_margin (orbitDeriv R.flow g)
    (contMDiff_orbitDeriv R.flow R.smooth g hg).continuous hn
  obtain ⟨p, hp, f, hf, hs, heq, hval, hder, ha⟩ :=
    planar_orbit_fourier_approximation R g hg A τ hA (min ε (δ / 2))
      (lt_min hε (by positivity))
  refine ⟨p, hp, f, hf, hs, heq,
    fun x ↦ (hval x).trans_le (min_le_left _ _),
    fun x ↦ (hder x).trans_le (min_le_left _ _), ha, ?_⟩
  intro x hz
  have he := (hder x).trans_le (min_le_right ε (δ / 2))
  rw [hz, zero_sub, norm_neg] at he
  have hm := hmargin x
  linarith

#print axioms planarOrbitConvolution_hasDerivAt
#print axioms contMDiff_planarOrbitConvolution
#print axioms planar_orbit_fourier_approximation
#print axioms planar_orbit_fourier_nonvanishing

end GlobalEmbedding.Paper
