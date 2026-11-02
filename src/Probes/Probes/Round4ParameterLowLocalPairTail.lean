import Smoothing.Round4ClosedPairFiniteGeometry
import Smoothing.Round3OuterLocalSetPair
import Smoothing.Round3OuterPreparedPair
import Smoothing.Round3OuterPreparedPairGain
import Smoothing.ParameterRound2CompactPair

/-!
# The named low-order tail on the original compact parameter set

The input and output norms are the unchanged original total-joint C2-map plus
C0-tensor norms. Compact coordinate domains prove every required fixed-order
finiteness guard. The only numerical input is the original low weighted pair
budget, and the high tail retains its actual original weighted norm. One
normalized product cutoff, signed kernel and scale produce the same native
map and native tensor in the tail and gain conclusions. The exact constant is twice the order-zero named pair constant.
Its raw geometry depth is two, independently of the kernel moment order;
it precedes every atlas, compact norm domain, raw preparation, field and scale.
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

local instance round4ParameterLowLocalPairTailChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round4ParameterLowLocalPairTailIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- The original low-order tail on a local compact parameter set. The input
budget is on the full actual sampling domains; the output is on the requested
original evaluation domains over K. The same SF/SH and uniform constant are
used, with no requirement that K exhaust the parameter manifold. -/
theorem round4Parameter_actual_local_low_pair_tail
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (r : ℕ) :
    let C := 2*round4PreparedPairConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp 0 r
    0 ≤ C ∧
      ∀ (pcount : ℕ) (A : BufferedAtlas M Es)
        (B : TensorBufferedChartFamily (Fin pcount) P Ep)
        (hA : IsSmoothBufferedAtlas A)
        (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
        (parameterSet : Set P)
        (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B parameterSet BP₀ TP Dp),
      rho ≤ min B.buffer A.buffer →
      ∀ (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep),
      (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
      (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
      (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
      (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
      ∀ (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ)),
      (∀ i, S i ⊆ round3OuterOriginalEvaluation A B parameterSet i) →
      ∀ ell t : ℝ, 0 < ell → ell ≤ t → t ≤ 1 →
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
        0 ell S ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        0 ell S).toReal ≤ C * budget * (ell/t)^r := by
  obtain ⟨hC,hpair⟩ := round4_actual_local_set_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho 0 r
  let C := round4PreparedPairConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp 0 r
  refine ⟨mul_nonneg (by norm_num) hC,?_⟩
  intro pcount A B hA hB parameterSet RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    S hS ell t hell helt ht1 u hu H hH budget hbudget
  have hp := hpair pcount A B hA hB parameterSet RS RP hbuffer Omega Q hOmega hQ hOT hQT
    hsource hparameter S hS ell ell t hell le_rfl helt ht1 u hu H hH budget hbudget
  dsimp only at hp ⊢
  let Sampling := incrementsOriginalEvaluation A B.chart Omega Q univ
  have hrfinite := parameterRound2_original_pair_on_compact_finite A B Omega Q hOmega hQ hOT hQT
    u hu H hH r t
  have hbase := add_le_add (parameterPaperAtlasCj_base_le_weighted 2 r t
      (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart) Sampling)
    (parameterPaperAtlasCj_base_le_weighted 0 r t
      (incrementsOriginalTensorCoordinates A B.chart H) (incrementsOriginalDifferentiation A B.chart) Sampling)
  have hzero : parameterLocalOriginalTotalPairWeighted A B u H 0 t Sampling ≤
      parameterLocalOriginalTotalPairWeighted A B u H r t Sampling := by
    simpa only [parameterLocalOriginalTotalPairWeighted,paperAtlasWeighted,
      Finset.sum_range_one,pow_zero,zero_add,one_mul] using hbase
  have hzb : (parameterLocalOriginalTotalPairWeighted A B u H 0 t Sampling).toReal ≤ budget :=
    (ENNReal.toReal_mono hrfinite hzero).trans hbudget
  have ha : 0 ≤ (ell/t)^r := pow_nonneg (div_nonneg hell.le (hell.trans_le helt).le) _
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  exact hp.2.2.2.1.trans ((mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hzb ha)) hC).trans_eq (by ring))

#print axioms round4Parameter_actual_local_low_pair_tail
end
end GlobalEmbedding.Continuation
