import Smoothing.ParameterLocalPreparedPair
import Smoothing.ParameterLocalPreparedPairGain
import Smoothing.ParameterRound2OriginalInputs

/-!
# Actual original-Core consumers for full parameter-manifold smoothing

Source: thm:repair's compact finite-dimensional parameter-manifold clause,
and the compact-torus parameter extension in prop:probes. The native fields
are the unchanged original D.F and D.H; the native Core, its full joint C2/C0
norms and its actual evaluation domains are unchanged. Genuine sampling-buffer
inclusions are used before applying a budget. The raw preparations construct
one actual normalized product cutoff. One fixed signed kernel and scale then
produce BOTH the original (6.4) tail and the original smoothing gain.

The theorem explicitly identifies the remaining atlas geometry inputs. It
neither infers sampling-buffer inclusion from source-inner inclusion nor
pretends that compactness alone supplies all raw transition-jet providers.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2CoreConsumersChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CoreConsumersIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- One constant, chosen before the original native data, controls both the
actual pair approximation and its actual weighted smoothing gain. The fields
are the original D.F and D.H, and every input bound comes from the original
Core on its own native coordinate domains. No output property is an input. -/
theorem exists_uniform_parameterRound2_originalCore_smoothing_pair
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : IncrementsOriginalNativeData n d N M P)
        (B : TensorBufferedChartFamily (Fin D.parameterCount) P Ep)
        (hchart : B.chart = D.parameterChart)
        (hA : IsSmoothBufferedAtlas D.atlas)
        (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
        (RS : TensorRawCutoffPreparation D.atlas BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B univ BP₀ TP Dp),
      rho ≤ min B.buffer D.atlas.buffer →
      IncrementsOriginalSmoothInputs D → D.parameterOpen = univ → D.parameterSet = univ →
      (∀ i, bufferedSamplingCoordinates D.atlas i ⊆ D.sourceNormDomain i) →
      (∀ i, tensorLocalSamplingCoordinates B i ⊆ D.parameterNormDomain i) →
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      incrementsOriginalCoreInputProfile D r t ≠ ⊤ →
      incrementsOriginalCoreInputProfile D m t ≠ ⊤ →
      ∀ budget : ℝ, (incrementsOriginalCoreInputProfile D r t).toReal ≤ budget →
      let mu := (volume : Measure (Ep × Es))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff D.atlas B
        (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let SF := parameterLocalMapSmoothing (parameterLocalProductFamily D.atlas B) mu K ell chi D.F
      let SH := tensorLocalParameterSmoothing D.atlas B hA mu K ell chi D.H
      ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ SF ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates D.atlas B.chart SH i)
        (incrementsOriginalDifferentiation D.atlas B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted D.atlas B
        (fun z => D.F z - SF z) (fun p x => D.H p x - SH p x)
        m tau (tensorLocalOriginalInner D.atlas B univ) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted D.atlas B
        (fun z => D.F z - SF z) (fun p x => D.H p x - SH p x)
        m tau (tensorLocalOriginalInner D.atlas B univ)).toReal ≤
        C * (budget * (ell/t)^r + (incrementsOriginalCoreInputProfile D m t).toReal * (tau/t)^r) ∧
      parameterLocalOriginalTotalPairWeighted D.atlas B SF SH
        m tau (tensorLocalOriginalInner D.atlas B univ) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted D.atlas B SF SH
        m tau (tensorLocalOriginalInner D.atlas B univ)).toReal ≤ C * budget := by
  obtain ⟨Ct, hCt, htail⟩ := exists_uniform_prepared_local_parameter_total_pair_smoothing_tail
    (n := n) (d := d) (q := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  obtain ⟨Cg, hCg, hgain⟩ := exists_uniform_prepared_local_parameter_total_pair_smoothing_gain
    (n := n) (d := d) (q := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  refine ⟨2 * max Ct Cg, mul_nonneg (by norm_num) (hCt.trans (le_max_left _ _)), ?_⟩
  intro D B hchart hA hB RS RP hbuffer hs hopen hset hsource hparameter
    tau ell t htau htaul helt ht1 hCr hCm budget hbudget
  have ht : 0 < t := htau.trans_le (htaul.trans helt)
  have hell : 0 < ell := htau.trans_le htaul
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hinputs := parameterRound2_original_full_parameter_inputs D B hchart hA hB hs hopen
  have hdomains := parameterRound2_sampling_subset_core_evaluation_univ
    D B hsource hparameter hset
  have hPr := parameterRound2_sampling_pair_finite_and_budget
    D B hchart hdomains r t hCr budget hbudget
  have hPm := parameterRound2_sampling_pair_finite_and_budget
    D B hchart hdomains m t hCm (incrementsOriginalCoreInputProfile D m t).toReal le_rfl
  have hP0 := parameterRound2_sampling_base_pair_finite_and_budget
    D B hchart hdomains r t hCr budget hbudget
  obtain ⟨W, hW, hUW, htailW⟩ := htail D.parameterCount D.atlas B hA hB univ RS RP hbuffer
  have hWu : W = univ := Set.Subset.antisymm (Set.subset_univ W) hUW
  subst W
  have htresult := htailW tau ell t htau htaul helt ht1 D.F hinputs.2.1 D.H hinputs.2.2
    hPr.1 hPm.1 (2 * budget) hPr.2
  have hgresult := hgain D.parameterCount D.atlas B hA hB univ RS RP hbuffer
    tau ell hell (helt.trans ht1) htau.le htaul D.F hinputs.2.1 D.H hinputs.2.2
    hP0.1 (2 * budget) hP0.2
  refine ⟨htresult.1, htresult.2.1, htresult.2.2.1, ?_, hgresult.2.2.1, ?_⟩
  · refine htresult.2.2.2.trans ?_
    have hratio0 : 0 ≤ (tau/t)^r := pow_nonneg (div_nonneg htau.le ht.le) _
    have hterm0 : 0 ≤ budget * (ell/t)^r +
        (incrementsOriginalCoreInputProfile D m t).toReal * (tau/t)^r :=
      add_nonneg (mul_nonneg hbudget0 (pow_nonneg (div_nonneg hell.le ht.le) _))
        (mul_nonneg ENNReal.toReal_nonneg hratio0)
    calc
      Ct * (2 * budget * (ell/t)^r +
        (parameterLocalOriginalTotalPairWeighted D.atlas B D.F D.H m t
          (tensorLocalOriginalSampling D.atlas B)).toReal * (tau/t)^r) ≤
        Ct * (2 * budget * (ell/t)^r +
          (2 * (incrementsOriginalCoreInputProfile D m t).toReal) * (tau/t)^r) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hPm.2 hratio0)) hCt
      _ = (2 * Ct) * (budget * (ell/t)^r +
          (incrementsOriginalCoreInputProfile D m t).toReal * (tau/t)^r) := by ring
      _ ≤ (2 * max Ct Cg) * (budget * (ell/t)^r +
          (incrementsOriginalCoreInputProfile D m t).toReal * (tau/t)^r) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left Ct Cg) (by norm_num)) hterm0
  · refine hgresult.2.2.2.trans ?_
    calc
      Cg * (2 * budget) = (2 * Cg) * budget := by ring
      _ ≤ (2 * max Ct Cg) * budget :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right Ct Cg) (by norm_num)) hbudget0

#print axioms exists_uniform_parameterRound2_originalCore_smoothing_pair
end
end GlobalEmbedding.Continuation
