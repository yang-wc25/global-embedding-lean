import NormalPolar.FullResponseTail
import Probes.ActualPrescribedProbeHessian

/-!
# Exact scale and parameter labels for the existing prescribed Hessian response

The already proved actual first-block response uses delta, tau, ell and an
injective finite label dictionary. This file keeps those actual labels,
embeds the original paired parameter space isometrically, and rewrites the
existing estimate at delta=t^10, tau=t^(6/5), ell=t. No spatial, parameter,
cutoff or repair-tail estimate is constructed here.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

/-- Extend the original paired parameters by zero in the prescribed finite
dictionary. The original sup norm and hence every original parameter ball
are preserved exactly. -/
def probeParameterEmbedding {r p : ℕ} (label : (Fin r × Bool) ↪ Fin p) :
    ProbeParameters r →ₗᵢ[ℝ] (Fin p → ℝ) where
  __ := Function.ExtendByZero.linearMap ℝ ℝ label
  norm_map' u := (label.injective.factorsThrough u).norm_extend (by simp)

@[simp] theorem probeParameterEmbedding_single {r p : ℕ}
    (label : (Fin r × Bool) ↪ Fin p) (k : Fin r × Bool) (a : ℝ) :
    probeParameterEmbedding label (Pi.single k a) = Pi.single (label k) a := by
  exact label.injective.extend_single k a

@[simp] theorem probeParameterEmbedding_norm {r p : ℕ}
    (label : (Fin r × Bool) ↪ Fin p) (u : ProbeParameters r) :
    ‖probeParameterEmbedding label u‖ = ‖u‖ := (probeParameterEmbedding label).norm_map u

/-- Native response directions become the literal original paired direction
after the isometric relabeling; no derivative coefficient is invented. -/
theorem fderiv_probeParameterEmbedding_single
    {r p : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (label : (Fin r × Bool) ↪ Fin p) (f : (Fin p → ℝ) → Y)
    (u : ProbeParameters r) (hf : DifferentiableAt ℝ f (probeParameterEmbedding label u))
    (k : Fin r × Bool) :
    fderiv ℝ (fun v ↦ f (probeParameterEmbedding label v)) u (Pi.single k 1) =
      fderiv ℝ f (probeParameterEmbedding label u) (Pi.single (label k) 1) := by
  have h := congrArg (fun L : ProbeParameters r →L[ℝ] Y ↦ L (Pi.single k 1))
    (hf.hasFDerivAt.comp u (probeParameterEmbedding label).toContinuousLinearMap.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, probeParameterEmbedding_single] using h

theorem probe_delta_div_tau_eq_sigma (t : ℝ) (ht : 0 < t) :
    t ^ (10 : ℕ) / t ^ ((6 : ℝ) / 5) = t ^ ((44 : ℝ) / 5) := by
  rw [← Real.rpow_natCast, ← Real.rpow_sub ht]
  norm_num

theorem probe_tau_div_ell_eq_fifth (t : ℝ) (ht : 0 < t) :
    t ^ ((6 : ℝ) / 5) / t = |t| ^ ((1 : ℝ) / 5) := by
  calc
    _ = t ^ ((6 : ℝ) / 5) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub ht, abs_of_pos ht]; norm_num

/-- The existing native first-block error is sigma times a vanishing
one-fifth-power modulus at the original scales, with no restriction t≤1
needed for this algebraic rewriting. Any provider's scale hypotheses remain
at that provider and are not silently imposed on the original family domain. -/
theorem native_hessian_response_original_scales
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (t : ℝ) (ht : 0 < t) (b : Bool) (theta C : ℝ) (R H : Y)
    (h : ‖R - ((t ^ (10 : ℕ) / t ^ ((6 : ℝ) / 5)) *
      (if b then Real.sin theta else Real.cos theta)) • H‖ ≤
        (t ^ (10 : ℕ) / t ^ ((6 : ℝ) / 5)) * (t ^ ((6 : ℝ) / 5) / t) * C) :
    ‖R - (t ^ ((44 : ℝ) / 5) * probeTrig b theta) • H‖ ≤
      t ^ ((44 : ℝ) / 5) * (C * |t| ^ ((1 : ℝ) / 5)) := by
  rw [probe_delta_div_tau_eq_sigma t ht, probe_tau_div_ell_eq_fifth t ht] at h
  convert h using 1
  · rfl
  · ring

theorem probe_fifth_modulus_nonneg (C : ℝ) (hC : 0 ≤ C) (t : ℝ) :
    0 ≤ C * |t| ^ ((1 : ℝ) / 5) := mul_nonneg hC (Real.rpow_nonneg (abs_nonneg t) _)

theorem probe_fifth_modulus_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ ↦ C * |t| ^ ((1 : ℝ) / 5)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ ↦ |t| ^ ((1 : ℝ) / 5)) :=
    (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 : ℝ) / 5)).comp continuous_abs
  have h : Tendsto (fun t : ℝ ↦ |t| ^ ((1 : ℝ) / 5)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_zero, Real.zero_rpow (by norm_num : (1 : ℝ) / 5 ≠ 0)] using
      (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  simpa only [mul_zero] using h.const_mul C

end GlobalEmbedding.NormalPolar
