import GlobalEmbedding.Offline.ChartSeriesLimit

/-!
# Joint smooth series and source-only metric limits

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `thm:repair`,
line 778. Smoothing and convergence take place in all source and parameter
variables, while the induced metric differentiates only the source variables.

The restriction to a fixed parameter is the actual map `x ↦ (p, x)`. Its native
manifold derivative, followed by the joint ambient differential, is exactly the
ambient differential of the slice. Thus total derivative convergence yields the
source derivative convergence required for the original induced metric, without
adding parameter directions to that metric.
-/

open Filter Set Manifold
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

variable {E H M EP HP P F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {J : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiate the actual fixed-parameter slice. The vector inserted into
the joint differential is the native derivative of `x ↦ (p,x)`, so the parameter
is held constant throughout this identity. -/
theorem mvfderiv_slice_apply
    {f : P × M → F} (p : P) (x : M)
    (hf : MDifferentiableAt (J.prod I) 𝓘(ℝ, F) f (p, x))
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ f (p, y)) x v =
      mvfderiv (J.prod I) f (p, x)
        (mfderiv I (J.prod I) (fun y : M ↦ (p, y)) x v) := by
  have hι : MDifferentiableAt I (J.prod I) (fun y : M ↦ (p, y)) x :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  simpa only [Function.comp_def] using mvfderiv_comp_apply x hf hι v

/-- Actual joint differential convergence implies actual source differential
convergence at every fixed parameter. Evaluation is at one fixed tangent vector
coming from the source inclusion, rather than at a parameter-dependent choice. -/
theorem tendsto_mvfderiv_slice_of_joint
    (fseq : ℕ → P × M → F) (f : P × M → F) (p : P) (x : M)
    (hseq : ∀ n, MDifferentiableAt (J.prod I) 𝓘(ℝ, F) (fseq n) (p, x))
    (hf : MDifferentiableAt (J.prod I) 𝓘(ℝ, F) f (p, x))
    (hD : Tendsto (fun n ↦ mvfderiv (J.prod I) (fseq n) (p, x)) atTop
      (𝓝 (mvfderiv (J.prod I) f (p, x))))
    (v : TangentSpace I x) :
    Tendsto (fun n ↦ mvfderiv I (fun y ↦ fseq n (p, y)) x v) atTop
      (𝓝 (mvfderiv I (fun y ↦ f (p, y)) x v)) := by
  simpa only [mvfderiv_slice_apply p x hf v, mvfderiv_slice_apply p x (hseq _) v,
    Function.comp_def] using
    ((continuous_eval_const
      (mfderiv I (J.prod I) (fun y : M ↦ (p, y)) x v)).tendsto
        (mvfderiv (J.prod I) f (p, x))).comp hD

/-- The parameter component of the inserted tangent vector is exactly zero.
This states the source-only character of the slice derivative without relying
on a definitional identification between a tangent space and its model space. -/
theorem mvfderiv_slice_apply_zero_parameter
    {f : P × M → F} (p : P) (x : M)
    (hf : MDifferentiableAt (J.prod I) 𝓘(ℝ, F) f (p, x))
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ f (p, y)) x v =
      mvfderiv (J.prod I) f (p, x)
        ((tangentSpaceCastModel (J.prod I) (p, x)).symm
          (0, tangentSpaceCastModel I x v)) := by
  rw [mvfderiv_slice_apply p x hf v, mfderiv_prod_right]
  rfl

/-- A jointly smooth repair series yields the prescribed source metric for
every parameter, with the same actual sum and the same iteration schedule.

Source: `thm:repair`, line 778. The hypothesis estimates native total coordinate
derivatives on the actual product model. `ChartSeriesLimit` gives joint smoothness
and total differential convergence. The proved fixed-parameter chain rule then
gives source-only differential convergence, which is precisely what the original
induced-metric limit theorem needs. Compactness of a parameter space belongs to
the earlier construction of these common bounds and schedules; this limit step
does not require an additional compactness hypothesis.
-/
theorem parametric_smooth_repair_series_metric_limit
    {N : ℕ} (F0 : P × M → EuclideanSpace ℝ (Fin N))
    (f : ℕ → P × M → EuclideanSpace ℝ (Fin N)) (t delta : ℕ → ℝ)
    (g : P → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (Hseq : ℕ → P → ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (hF0 : ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F0)
    (ht : Summable t)
    (hchart : ∀ z : P × M, ∃ U : Set (EP × E),
      IsOpen U ∧ extChartAt (J.prod I) z z ∈ U ∧
      (∀ n, ContDiffOn ℝ ∞ (f n ∘ (extChartAt (J.prod I) z).symm) U) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∃ K : ℕ, ∀ n ≥ K, ∀ y ∈ U,
        ‖iteratedFDerivWithin ℝ k (f n ∘ (extChartAt (J.prod I) z).symm) U y‖ ≤ C * t n))
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hH : ∀ (p : P) (x : M) (v w : TangentSpace I x),
      ∃ C : ℝ, ∀ᶠ n in atTop, ‖Hseq n p x v w‖ ≤ C)
    (hdefect : ∀ n p x, g p x - GlobalEmbedding.Paper.inducedMetric (I := I)
      (fun y ↦ F0 (p, y) + ∑ j ∈ Finset.range n, f j (p, y)) x =
        delta n ^ 2 • Hseq n p x) :
    (∀ z, Summable (fun n ↦ f n z)) ∧
    ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun z ↦ F0 z + ∑' n, f n z) ∧
    (∀ p, ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun x ↦ F0 (p, x) + ∑' n, f n (p, x)) ∧
      GlobalEmbedding.Paper.inducedMetric (I := I)
        (fun x ↦ F0 (p, x) + ∑' n, f n (p, x)) = g p) := by
  have hs := smooth_base_add_tsum_and_tendsto_mvfderiv F0 f t hF0 ht hchart
  have hterm (n : ℕ) : ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (f n) := by
    intro z
    obtain ⟨U, hU, hz, hf, _hbound⟩ := hchart z
    exact contMDiffAt_of_contDiffOn_extChartAt hU hz (hf n)
  have hpartial (K : ℕ) : ContMDiff (J.prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun z ↦ F0 z + ∑ n ∈ Finset.range K, f n z) :=
    hF0.add (ContMDiff.sum fun n _hn ↦ hterm n)
  have hsource (p : P) (x : M) (v : TangentSpace I x) :
      Tendsto (fun K ↦ mvfderiv I
        (fun y ↦ F0 (p, y) + ∑ n ∈ Finset.range K, f n (p, y)) x v) atTop
        (𝓝 (mvfderiv I (fun y ↦ F0 (p, y) + ∑' n, f n (p, y)) x v)) :=
    tendsto_mvfderiv_slice_of_joint
      (fun K z ↦ F0 z + ∑ n ∈ Finset.range K, f n z)
      (fun z ↦ F0 z + ∑' n, f n z) p x
      (fun K ↦ (hpartial K).mdifferentiableAt (by simp))
      (hs.2.1.mdifferentiableAt (by simp)) (hs.2.2 (p, x)) v
  have hmetric := inducedMetric_eq_of_tendsto_normalized_defect_family
    (fun K p x ↦ F0 (p, x) + ∑ n ∈ Finset.range K, f n (p, x))
    (fun p x ↦ F0 (p, x) + ∑' n, f n (p, x)) g Hseq delta hsource hdelta hH hdefect
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro p
  refine ⟨?_, hmetric p⟩
  simpa only [Function.comp_def] using
    hs.2.1.comp (contMDiff_const.prodMk contMDiff_id :
      ContMDiff I (J.prod I) ∞ (fun x : M ↦ (p, x)))

#print axioms mvfderiv_slice_apply
#print axioms tendsto_mvfderiv_slice_of_joint
#print axioms mvfderiv_slice_apply_zero_parameter
#print axioms parametric_smooth_repair_series_metric_limit

end GlobalEmbedding.Offline
