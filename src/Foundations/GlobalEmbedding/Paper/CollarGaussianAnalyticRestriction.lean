import GlobalEmbedding.Paper.CollarGaussianApproximation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Real analyticity of the same literal normalized Gaussian

Source: `main.tex`, Proposition `prop:collar`, proof line 520.
Native Banach-algebra exponential on a compact support and native integration CLMs give
analyticity directly. No univariate holomorphy conversion or Gaussian estimate is needed.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The actual scalar normalized Gaussian convolution of continuous compact data is real
analytic. On the original compact support the exponent is a finite quadratic polynomial
in the real Banach algebra of continuous functions. Apply native analytic exponential,
multiply the original data and compose the native L1 integration CLM. Native subtype
integration identifies precisely the original whole-space integral, including empty support. -/
theorem collarGaussian_scalar_analytic {d : ℕ} (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    AnalyticOnNhd ℝ (fun x : EuclideanSpace ℝ (Fin d) ↦
      ∫ y : EuclideanSpace ℝ (Fin d),
        ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) * f y) univ := by
  let K := tsupport f
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let : MeasureSpace K := Measure.Subtype.measureSpace
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ (isClosed_tsupport f).measurableSet.nullMeasurableSet]
    exact hc.measure_lt_top⟩
  let Y (i : Fin d) : C(K, ℝ) :=
    ⟨fun y ↦ y.val i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩
  let Q (x : EuclideanSpace ℝ (Fin d)) : C(K, ℝ) :=
    (-ε⁻¹) • ∑ i : Fin d, (ContinuousMap.const K (x i) - Y i) ^ 2
  let w : C(K, ℝ) := ⟨fun y ↦ f y.val, hf.comp continuous_subtype_val⟩
  let a := (Real.pi * ε) ^ (-(d : ℝ) / 2)
  let T (x : EuclideanSpace ℝ (Fin d)) : C(K, ℝ) := a • (NormedSpace.exp (Q x) * w)
  let J : C(K, ℝ) →L[ℝ] ℝ :=
    (L1.integralCLM' ℝ).comp (ContinuousMap.toLp 1 volume ℝ)
  have hJ (v : C(K, ℝ)) : J v = ∫ y : K, v y := by
    change (L1.integralCLM' ℝ) (ContinuousMap.toLp 1 volume ℝ v) = _
    rw [← L1.integral_eq' ℝ, L1.integral_eq_integral]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp volume v)
  have hT (x : EuclideanSpace ℝ (Fin d)) : AnalyticAt ℝ T x := by
    have hQ : AnalyticAt ℝ Q x := by
      change AnalyticAt ℝ (fun z ↦ (-ε⁻¹) •
        ∑ i : Fin d, (ContinuousMap.const K (z i) - Y i) ^ 2) x
      apply AnalyticAt.fun_const_smul
      apply Finset.analyticAt_fun_sum
      intro i _
      have hi : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin d) ↦ z i) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).analyticAt x
      let C : ℝ →L[ℝ] C(K, ℝ) := ContinuousLinearMap.const ℝ K
      have hconst := (C.analyticAt (x i)).comp
        (f := fun z : EuclideanSpace ℝ (Fin d) ↦ z i) hi
      exact (hconst.fun_sub analyticAt_const).fun_pow 2
    change AnalyticAt ℝ (fun z ↦ a • (NormedSpace.exp (Q z) * w)) x
    exact (((NormedSpace.exp_analytic (Q x)).comp hQ).fun_mul
      (analyticAt_const (v := w))).fun_const_smul (c := a)
  have hpoint (x : EuclideanSpace ℝ (Fin d)) (y : K) :
      T x y = (a * Real.exp (-‖x - y.val‖ ^ 2 / ε)) * f y.val := by
    have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ y)
      (ContinuousMap.evalCLM ℝ y).continuous (Q x)
    change NormedSpace.exp (Q x) y = NormedSpace.exp (Q x y) at he
    change a * (NormedSpace.exp (Q x) y * f y.val) = _
    rw [he, ← Real.exp_eq_exp_ℝ]
    have hQ : Q x y = -‖x - y.val‖ ^ 2 / ε := by
      have hY (i : Fin d) : Y i y = y.val i := rfl
      simp only [Q, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
        ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply, hY,
        smul_eq_mul]
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [PiLp.sub_apply]
      ring
    rw [hQ]
    ring
  have heq : (fun x ↦ J (T x)) = fun x : EuclideanSpace ℝ (Fin d) ↦
      ∫ y : EuclideanSpace ℝ (Fin d), (a * Real.exp (-‖x - y‖ ^ 2 / ε)) * f y := by
    funext x
    rw [hJ]
    calc
      (∫ y : K, T x y) = ∫ y : K, (a * Real.exp (-‖x - y.val‖ ^ 2 / ε)) * f y.val :=
        integral_congr_ae (ae_of_all _ (hpoint x))
      _ = ∫ y in K, (a * Real.exp (-‖x - y‖ ^ 2 / ε)) * f y :=
        integral_subtype (s := K) (isClosed_tsupport f).measurableSet
          (fun y ↦ (a * Real.exp (-‖x - y‖ ^ 2 / ε)) * f y)
      _ = ∫ y, (a * Real.exp (-‖x - y‖ ^ 2 / ε)) * f y :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by
          rw [image_eq_zero_of_notMem_tsupport hy, mul_zero])
  intro x _
  rw [← heq]
  exact (J.analyticAt (T x)).comp (hT x)

/-- The SAME literal normalized Gaussian of the accepted approximation provider is real
analytic in every finite dimension, with its original Euclidean target and measure. The
stronger continuous-input hypothesis suffices; no width sign is needed for analyticity of
the totalized expression. Thus every original positive-width smooth compact approximation
has actual omega regularity. Reuse the scalar compact-algebra proof coordinatewise and
native Bochner projection; no Gaussian convergence or complex entire proof is repeated. -/
theorem collar_gaussian_analytic_restriction {d N : ℕ} (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin N))
    (hf : Continuous f) (hc : HasCompactSupport f) :
    AnalyticOnNhd ℝ (fun x : EuclideanSpace ℝ (Fin d) ↦
      ∫ y : EuclideanSpace ℝ (Fin d),
        ((Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / ε)) • f y) univ := by
  let a := (Real.pi * ε) ^ (-(d : ℝ) / 2)
  let g (x y : EuclideanSpace ℝ (Fin d)) := a * Real.exp (-‖x - y‖ ^ 2 / ε)
  let H (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin N) :=
    (EuclideanSpace.equiv (Fin N) ℝ).symm (fun j ↦ ∫ y, g x y * f y j)
  have hH (x : EuclideanSpace ℝ (Fin d)) : AnalyticAt ℝ H x := by
    apply (EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap.analyticAt _ |>.comp
    apply AnalyticAt.pi
    intro j
    have hfj : Continuous (fun y ↦ f y j) := (EuclideanSpace.proj j).continuous.comp hf
    have hcj : HasCompactSupport (fun y ↦ f y j) :=
      hc.comp_left (show (EuclideanSpace.proj j :
        EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) 0 = 0 from map_zero _)
    exact collarGaussian_scalar_analytic ε _ hfj hcj x (mem_univ x)
  have hi (x : EuclideanSpace ℝ (Fin d)) : Integrable (fun y ↦ g x y • f y) := by
    have hg : Continuous (g x) := by fun_prop
    exact (hg.smul hf).integrable_of_hasCompactSupport hc.smul_left
  have heq : H = fun x : EuclideanSpace ℝ (Fin d) ↦ ∫ y, g x y • f y := by
    funext x
    apply (EuclideanSpace.equiv (Fin N) ℝ).injective
    funext j
    rw [show H x = (EuclideanSpace.equiv (Fin N) ℝ).symm
      (fun j ↦ ∫ y, g x y * f y j) from rfl,
      ContinuousLinearEquiv.apply_symm_apply]
    have hproj := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm (hi x)
    change (∫ y, g x y * f y j) = (∫ y, g x y • f y) j
    simpa only [map_smul, smul_eq_mul, EuclideanSpace.proj, PiLp.proj_apply] using hproj
  intro x _
  rw [← heq]
  exact hH x

end GlobalEmbedding.Paper
