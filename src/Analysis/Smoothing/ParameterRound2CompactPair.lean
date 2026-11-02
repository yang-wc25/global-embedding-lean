import Smoothing.ParameterLocalPreparedPair
import Smoothing.ParameterLocalPreparedPairGain
import Smoothing.ParameterRound2PreparedGeometry

/-!
# The actual full-parameter pair on genuine compact original norm domains

The input and output norms are the unchanged original total-joint C2-map plus
C0-tensor norms. Compact coordinate domains prove every required fixed-order
finiteness guard. The only numerical input is the original low weighted pair
budget, and the high tail retains its actual original weighted norm. One
normalized product cutoff, signed kernel and scale produce the same native
map and native tensor in the tail and gain conclusions. Uniform constants
precede every atlas, compact norm domain, raw preparation, field and scale.
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

local instance parameterRound2CompactPairChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2CompactPairIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- Every fixed actual pair norm is finite on true compact original coordinate
pieces. Smoothness is of the same fields in the original full joint domains. -/
theorem parameterRound2_original_pair_on_compact_finite
    {pcount : ℕ} (A : BufferedAtlas M Es)
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (u : P × M → Ey)
    (hu : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i))
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i)) (j : ℕ) (t : ℝ) :
    parameterLocalOriginalTotalPairWeighted A B u H j t
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≠ ⊤ := by
  let O := incrementsOriginalDifferentiation A B.chart
  let S := incrementsOriginalEvaluation A B.chart Omega Q univ
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B.chart
  have hS : ∀ i, IsCompact (S i) := parameterRound2_originalEvaluation_univ_compact
    A B.chart Omega Q hOmega hQ hOmegaTarget hQTarget
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  exact ENNReal.add_ne_top.mpr
    ⟨parameterRound2_paperAtlasWeighted_finite_of_compact _ O S S hO hS
      (fun _ => Subset.rfl) hSO hu 2 j t,
     parameterRound2_paperAtlasWeighted_finite_of_compact _ O S S hO hS
      (fun _ => Subset.rfl) hSO hH 0 j t⟩

/-- The complete actual pair estimates, with finiteness derived from compact
original norm pieces and one constant chosen before all varying geometry and
input fields. The high tail uses the exact original input norm on those pieces. -/
theorem exists_uniform_parameterRound2_compact_pair_smoothing
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (pcount : ℕ) (A : BufferedAtlas M Es)
        (B : TensorBufferedChartFamily (Fin pcount) P Ep)
        (hA : IsSmoothBufferedAtlas A)
        (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
        (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B univ BP₀ TP Dp),
      rho ≤ min B.buffer A.buffer →
      ∀ (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep),
      (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
      (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
      (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
      (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ budget : ℝ,
      (parameterLocalOriginalTotalPairWeighted A B u H r t
        (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
      let mu := (volume : Measure (Ep × Es))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff A B
        (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ SF ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau (tensorLocalOriginalInner A B univ) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau (tensorLocalOriginalInner A B univ)).toReal ≤
        C * (budget * (ell/t)^r +
          (parameterLocalOriginalTotalPairWeighted A B u H m t
            (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal * (tau/t)^r) ∧
      parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau (tensorLocalOriginalInner A B univ) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau (tensorLocalOriginalInner A B univ)).toReal ≤ C * budget := by
  obtain ⟨Ct, hCt, htail⟩ := exists_uniform_prepared_local_parameter_total_pair_smoothing_tail
    (n := n) (d := d) (q := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  obtain ⟨Cg, hCg, hgain⟩ := exists_uniform_prepared_local_parameter_total_pair_smoothing_gain
    (n := n) (d := d) (q := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  refine ⟨max Ct Cg, hCt.trans (le_max_left _ _), ?_⟩
  intro pcount A B hA hB RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget
    hsource hparameter tau ell t htau htaul helt ht1 u hu H hH budget hbudget
  have ht : 0 < t := htau.trans_le (htaul.trans helt)
  have hell : 0 < ell := htau.trans_le htaul
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hfull (j : ℕ) := parameterRound2_original_pair_on_compact_finite
    A B Omega Q hOmega hQ hOmegaTarget hQTarget u hu H hH j t
  have hdomains : ∀ i, tensorLocalOriginalSampling A B i ⊆
      incrementsOriginalEvaluation A B.chart Omega Q univ i := by
    intro i y hy
    exact ⟨hy.1, hsource i.1 hy.2.1, hparameter i.2 hy.2.2.1, Set.mem_univ _⟩
  have hle (j : ℕ) : parameterLocalOriginalTotalPairWeighted A B u H j t (tensorLocalOriginalSampling A B) ≤
      parameterLocalOriginalTotalPairWeighted A B u H j t
        (incrementsOriginalEvaluation A B.chart Omega Q univ) :=
    add_le_add (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hdomains)
      (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hdomains)
  have hsfinite (j : ℕ) := ne_top_of_le_ne_top (hfull j) (hle j)
  have hsle (j : ℕ) := ENNReal.toReal_mono (hfull j) (hle j)
  have hbase := add_le_add (parameterPaperAtlasCj_base_le_weighted 2 r t
      (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
        (tensorLocalOriginalSampling A B))
    (parameterPaperAtlasCj_base_le_weighted 0 r t
      (incrementsOriginalTensorCoordinates A B.chart H) (incrementsOriginalDifferentiation A B.chart)
        (tensorLocalOriginalSampling A B))
  have hbasefinite := ne_top_of_le_ne_top (hsfinite r) hbase
  have hbasebudget := (ENNReal.toReal_mono (hsfinite r) hbase).trans ((hsle r).trans hbudget)
  obtain ⟨W, hW, hUW, htailW⟩ := htail pcount A B hA hB univ RS RP hbuffer
  have hWu : W = univ := Set.Subset.antisymm (Set.subset_univ W) hUW
  subst W
  have htresult := htailW tau ell t htau htaul helt ht1 u hu H hH
    (hsfinite r) (hsfinite m) budget ((hsle r).trans hbudget)
  have hgresult := hgain pcount A B hA hB univ RS RP hbuffer
    tau ell hell (helt.trans ht1) htau.le htaul u hu H hH hbasefinite budget hbasebudget
  refine ⟨htresult.1, htresult.2.1, htresult.2.2.1, ?_, hgresult.2.2.1, ?_⟩
  · refine htresult.2.2.2.trans ?_
    have hratio0 : 0 ≤ (tau/t)^r := pow_nonneg (div_nonneg htau.le ht.le) _
    have hterm0 : 0 ≤ budget * (ell/t)^r +
        (parameterLocalOriginalTotalPairWeighted A B u H m t
          (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal * (tau/t)^r :=
      add_nonneg (mul_nonneg hbudget0 (pow_nonneg (div_nonneg hell.le ht.le) _))
        (mul_nonneg ENNReal.toReal_nonneg hratio0)
    exact (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hsle m) hratio0)) hCt).trans
      (mul_le_mul_of_nonneg_right (le_max_left Ct Cg) hterm0)
  · exact hgresult.2.2.2.trans
      (mul_le_mul_of_nonneg_right (le_max_right Ct Cg) hbudget0)

#print axioms parameterRound2_original_pair_on_compact_finite
#print axioms exists_uniform_parameterRound2_compact_pair_smoothing
end
end GlobalEmbedding.Continuation
