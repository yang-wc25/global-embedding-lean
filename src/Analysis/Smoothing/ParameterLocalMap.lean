import Smoothing.ParameterLocalProduct

/-!
# One actual map smoothing for a noncovering buffered chart family

The integral and cutoff sum are actual functions. Smoothness needs local
coordinate smoothness only; the family need not cover the whole manifold.
The error identity needs the square partition only at the evaluation point,
and hence holds as a genuine germ on an open neighborhood of the parameter
set supplied by TensorLocalNormalization. No local error estimate is assumed.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set Filter MeasureTheory Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {ι X E F : Type*} [Fintype ι] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The same finite integral formula, now without a fictitious global cover. -/
def parameterLocalMapSmoothing (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ) (u : X → F) (x : X) : F :=
  ∑ i, chi i x ^ 2 • tensorLocalChartConvolution C mu K ell u i x

theorem parameterLocalMapSmoothing_eq_buffered (A : BufferedAtlas X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : Fin A.count → X → ℝ) (u : X → F) :
    parameterLocalMapSmoothing (tensorChartFamilyOfAtlas A) mu K ell chi u =
      bufferedSmoothing A mu K ell chi u := rfl

/-- Actual support is retained, including at every chart boundary. -/
theorem parameterLocalMapSmoothing_tsupport_subset
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ) (u : X → F) :
    tsupport (parameterLocalMapSmoothing C mu K ell chi u) ⊆ ⋃ i, tsupport (chi i) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_closure)
  intro x hx
  by_contra h
  have hchi (i : ι) : chi i x = 0 := by
    apply notMem_support.mp
    intro hi
    exact h (mem_iUnion.mpr ⟨i, subset_tsupport (chi i) hi⟩)
  exact hx (by simp only [parameterLocalMapSmoothing, hchi, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_smul, Finset.sum_const_zero])

/-- The true global error decomposition uses the partition only at x. -/
theorem parameterLocalMapSmoothing_error_at
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (u : X → F) (x : X) (hpartition : ∑ i, chi i x ^ 2 = 1) :
    parameterLocalMapSmoothing C mu K ell chi u x - u x =
      ∑ i, chi i x ^ 2 • (tensorLocalConvolution C mu K ell u i (C.chart i x) -
        tensorLocalCoordinateExtension C u i (C.chart i x)) := by
  have hsingle (i : ι) :
      chi i x ^ 2 • tensorLocalChartConvolution C mu K ell u i x - chi i x ^ 2 • u x =
      chi i x ^ 2 • (tensorLocalConvolution C mu K ell u i (C.chart i x) -
        tensorLocalCoordinateExtension C u i (C.chart i x)) := by
    by_cases hi : chi i x = 0
    · simp only [hi,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_smul,sub_zero]
    · have hx := C.inner_subset i (hsupport i (subset_tsupport (chi i) hi))
      rw [tensorLocalChartConvolution,Set.indicator_of_mem hx,Function.comp_apply,
        tensorLocalCoordinateExtension,Set.indicator_of_mem ((C.chart i).map_source hx),
        Function.comp_apply,(C.chart i).left_inv hx]
      exact (smul_sub _ _ _).symm
  have hsum : (∑ i, chi i x ^ 2 • u x) = u x := by
    rw [← Finset.sum_smul,hpartition,one_smul]
  unfold parameterLocalMapSmoothing
  conv_lhs => rw [← hsum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => hsingle i)

/-- An open local square partition gives the actual error identity on a
neighborhood, so downstream derivatives can use it as an equality of germs. -/
theorem parameterLocalMapSmoothing_error_eventuallyEq
    (C : TensorBufferedChartFamily ι X E) (mu : Measure E)
    (K : E → ℝ) (ell : ℝ) (chi : ι → X → ℝ)
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (u : X → F) {U : Set X} (hU : IsOpen U)
    (hpartition : ∀ x ∈ U, ∑ i, chi i x ^ 2 = 1) {x : X} (hx : x ∈ U) :
    (fun z => parameterLocalMapSmoothing C mu K ell chi u z-u z) =ᶠ[𝓝 x]
      (fun z => ∑ i, chi i z ^ 2 • (tensorLocalConvolution C mu K ell u i (C.chart i z) -
        tensorLocalCoordinateExtension C u i (C.chart i z))) := by
  filter_upwards [hU.mem_nhds hx] with z hz
  exact parameterLocalMapSmoothing_error_at C mu K ell chi hsupport u z (hpartition z hz)

variable [BorelSpace E] [FiniteDimensional ℝ E]
    [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- The actual map is jointly smooth from the original local coordinate
regularity, without any smoothness or chart-cover premise away from the family. -/
theorem parameterLocalMapSmoothing_contMDiff
    (C : TensorBufferedChartFamily ι X E)
    (hchart : ∀ i, C.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ C.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → X → ℝ) (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hsupport : ∀ i, tsupport (chi i) ⊆ C.inner i)
    (u : X → F)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (C.chart i).symm) (C.chart i).target) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (parameterLocalMapSmoothing C mu K ell chi u) := by
  exact ContMDiff.sum fun i _ => tensorLocalWeightedConvolution_contMDiff C hchart mu hK hcompact
    hsupp hrho hell hell1 chi hchi hsupport u i (hu i)

#print axioms parameterLocalMapSmoothing_contMDiff
#print axioms parameterLocalMapSmoothing_error_eventuallyEq
#print axioms parameterLocalMapSmoothing_tsupport_subset
end
end GlobalEmbedding.Continuation
