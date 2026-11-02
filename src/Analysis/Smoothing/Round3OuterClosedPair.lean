import Smoothing.Round3OuterLocalSetPair
import Smoothing.Round3OuterPreparedPair
import Smoothing.Round3OuterPreparedPairGain
import Smoothing.ParameterRound2CompactPair

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

local instance round3Outer_closedParameterSameDomainPairChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round3Outer_closedParameterSameDomainPairIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-! A global parameter preparation supplies the SAME fixed compact sampling
norm on input and output. This is the domain closure needed for repeated
repair on a compact parameter manifold. The source and parameter buffers,
original full joint norms, signed kernel, and common SF/SH remain literal.
No larger-domain budget is inferred from a smaller one. -/
theorem round3Outer_exists_uniform_closed_parameter_same_domain_pair
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
      let S := incrementsOriginalEvaluation A B.chart Omega Q univ
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
        m tau S ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau S).toReal ≤
        C * (budget * (ell/t)^r +
          (parameterLocalOriginalTotalPairWeighted A B u H m t
            (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal * (tau/t)^r) ∧
      parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau S ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B SF SH
        m tau S).toReal ≤ C * budget := by
  obtain ⟨C,hC,hpair⟩ := round3Outer_exists_uniform_parameterRound2_local_set_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp rho hrho m r
  refine ⟨C,hC,?_⟩
  intro pcount A B hA hB RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    tau ell t htau htaul helt ht1 u hu H hH budget hbudget
  exact hpair pcount A B hA hB univ RS RP hbuffer Omega Q hOmega hQ hOT hQT hsource hparameter
    (incrementsOriginalEvaluation A B.chart Omega Q univ)
    (fun _ _ hy => ⟨hy.1,Set.mem_univ _⟩)
    tau ell t htau htaul helt ht1 u hu H hH budget hbudget

#print axioms round3Outer_exists_uniform_closed_parameter_same_domain_pair
end
end GlobalEmbedding.Continuation
