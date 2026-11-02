import Smoothing.ParameterRound2CompactPair

/-!
# Constructed global smoothing for maps and native tensors with parameters

This is the actual compact-manifold consumer of the chart, bump, transition,
normalization, finite-moment kernel and native tensor proofs. Both manifolds
are the same compact smooth Hausdorff manifolds supplied by the caller. All
geometry, cutoffs and norm domains are constructed before any field is given.
For every fixed pair of orders, one constant then works for every field,
budget and permitted scale. The norm and (6.4) remain the original full joint
base-two map plus base-zero native tensor expression.
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
    [CompactSpace M] [T2Space M] [CompactSpace P] [T2Space P]

local instance parameterRound2GlobalPairChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2GlobalPairIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Eparameter" => EuclideanSpace ℝ (Fin d)
local notation "Esource" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- Actual global parameter-map/tensor smoothing, with all chart geometry and
raw jet profiles constructed from compactness and native smooth charts. There
are no preparation, norm-finiteness or output-estimate hypotheses. The only
numerical input is the original low weighted pair bound. -/
theorem parameterRound2_exists_global_compact_parameter_pair_smoothing :
    ∃ (A : BufferedAtlas M Esource) (B : BufferedAtlas P Eparameter),
      ∃ (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B),
      ∃ (Omega : Fin A.count → Set Esource) (Q : Fin B.count → Set Eparameter),
      (∀ i, IsCompact (Omega i) ∧ Omega i ⊆ (A.chart i).target ∧
        closure (bufferedSamplingCoordinates A i) ⊆ Omega i) ∧
      (∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
        closure (bufferedSamplingCoordinates B i) ⊆ Q i) ∧
      ∃ (rho : ℝ) (hrho : 0 < rho), rho ≤ min B.buffer A.buffer ∧
      ∃ chi : (Fin A.count × Fin B.count) → P × M → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, ℝ) ∞ (chi i)) ∧
      (∀ z, ∑ i, chi i z ^ 2 = 1) ∧
      (∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A (tensorChartFamilyOfAtlas B)).inner i) ∧
      ∀ m r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Esource) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ budget : ℝ,
      (parameterLocalOriginalTotalPairWeighted A (tensorChartFamilyOfAtlas B) u H r t
        (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
      let mu := (volume : Measure (Eparameter × Esource))
      let K := fixedSmoothingKernel mu rho hrho r
      let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A (tensorChartFamilyOfAtlas B)) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A (tensorChartFamilyOfAtlas B) hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ SF ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted A (tensorChartFamilyOfAtlas B)
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau (tensorLocalOriginalInner A (tensorChartFamilyOfAtlas B) univ) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A (tensorChartFamilyOfAtlas B)
        (fun z => u z - SF z) (fun p x => H p x - SH p x)
        m tau (tensorLocalOriginalInner A (tensorChartFamilyOfAtlas B) univ)).toReal ≤
        C * (budget * (ell/t)^r +
          (parameterLocalOriginalTotalPairWeighted A (tensorChartFamilyOfAtlas B) u H m t
            (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal * (tau/t)^r) ∧
      parameterLocalOriginalTotalPairWeighted A (tensorChartFamilyOfAtlas B) SF SH
        m tau (tensorLocalOriginalInner A (tensorChartFamilyOfAtlas B) univ) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A (tensorChartFamilyOfAtlas B) SF SH
        m tau (tensorLocalOriginalInner A (tensorChartFamilyOfAtlas B) univ)).toReal ≤ C * budget := by
  obtain ⟨A, hA, BS₀, TS, hBS₀, hTS, ⟨RS⟩, Omega, hOmega⟩ :=
    parameterRound2_exists_compact_prepared_bufferedAtlas (E := Esource) (X := M)
  obtain ⟨B, hB, BP₀, TP, hBP₀, hTP, ⟨RPg⟩, Q, hQ⟩ :=
    parameterRound2_exists_compact_prepared_bufferedAtlas (E := Eparameter) (X := P)
  let Bl := tensorChartFamilyOfAtlas B
  let RP := parameterRound2_localPreparationOfGlobal B RPg (univ : Set P)
  let rho := min B.buffer A.buffer
  have hrho : 0 < rho := lt_min B.buffer_pos A.buffer_pos
  let chi := parameterLocalProductCutoff A Bl
    (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
  obtain ⟨Bc, hBc, hprep⟩ := exists_uniform_local_product_smoothing_providers
    (Es := Esource) (Ep := Eparameter) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP A.supportDegree B.supportDegree
  obtain ⟨W, hW, hUW, hchi, hpart, hsupp, _hD, _hw, _ht⟩ :=
    hprep B.count A Bl hA hB.chart_mem univ RS RP
  have hpartAll : ∀ z, ∑ i, chi i z ^ 2 = 1 := fun z => hpart z (hUW (Set.mem_univ z.1))
  refine ⟨A, B, hA, hB, Omega, Q, hOmega, hQ, rho, hrho, le_rfl,
    chi, hchi, hpartAll, hsupp, ?_⟩
  intro m r
  obtain ⟨C, hC, hconsumer⟩ := exists_uniform_parameterRound2_compact_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP A.supportDegree B.supportDegree rho hrho m r
  refine ⟨C, hC, ?_⟩
  exact hconsumer B.count A Bl hA hB.chart_mem RS RP le_rfl Omega Q
    (fun i => (hOmega i).1) (fun i => (hQ i).1)
    (fun i => (hOmega i).2.1) (fun i => (hQ i).2.1)
    (fun i => subset_closure.trans (hOmega i).2.2)
    (fun i => subset_closure.trans (hQ i).2.2)

#print axioms parameterRound2_exists_global_compact_parameter_pair_smoothing
end
end GlobalEmbedding.Continuation
