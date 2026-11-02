import Smoothing.ParameterRound2CoreConsumers
import Smoothing.ParameterRound2GlobalPair
import GlobalEmbedding.Offline.RepairMetricIdentity

/-!
# The actual joint smoother in the original native repair identity (6.6)

The old defect is defined from the same native G and the target metric. Both
SG and SH are the actual constructed map/tensor convolutions with the SAME
normalized cutoff, moment kernel and scale. The increment error is the literal
original induced-metric error at SG, with the actual smoothed target SH minus
the reserve. The new defect is defined from the actual update G+U. Applying
the native quadratic identity in each source slice proves (6.6) pointwise on
the full parameter manifold. No error identity or squared smoothing defect
is assumed or inserted.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2RepairIdentityChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2RepairIdentityIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Eparameter" => EuclideanSpace ℝ (Fin d)
local notation "Esource" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- Joint native smoothness restricts to the literal source slice. The
parameter derivative is never part of the induced metric differential. -/
theorem parameterRound2_native_source_slice_contMDiff
    {G : P × M → Ey} (hG : ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ G) (p : P) :
    ContMDiff 𝓘(ℝ, Esource) 𝓘(ℝ, Ey) ∞ (fun x => G (p, x)) := by
  rw [modelWithCornersSelf_prod] at hG
  exact hG.comp (contMDiff_const.prodMk contMDiff_id :
    ContMDiff 𝓘(ℝ, Esource) (𝓘(ℝ, Eparameter).prod 𝓘(ℝ, Esource)) ∞ (fun x : M => (p, x)))

/-- Original (6.6) for the SAME actual joint map/tensor smoother and the
literal finite-increment metric error. Both normalized defects are derived
from actual maps. This is the concrete algebraic repair consumer. -/
theorem parameterRound2_actual_smoothing_defect_identity
    (A : BufferedAtlas M Esource)
    (B : TensorBufferedChartFamily (Fin pcount) P Eparameter)
    (hA : IsSmoothBufferedAtlas A)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Eparameter) ∞ P)
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
    (RP : TensorLocalRawPreparation B univ BP₀ TP Dp)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer)
    (r : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (G U : P × M → Ey)
    (hG : ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ G)
    (hU : ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ U)
    (delta deltaNext : ℝ) (hdelta : delta ≠ 0) (hdeltaNext : deltaNext ≠ 0)
    (hstar h0 : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Esource) x)) :
    let mu := (volume : Measure (Eparameter × Esource))
    let K := fixedSmoothingKernel mu rho hrho r
    let chi := parameterLocalProductCutoff A B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let H := fun p x => (delta ^ 2)⁻¹ •
      (hstar p x - inducedMetric (I := 𝓘(ℝ, Esource)) (fun y => G (p, y)) x)
    let SG := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi G
    let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
    let E := incrementsOriginalMetricError SG U
      (fun p x => SH p x - (deltaNext / delta) ^ 2 • h0 p x) delta
    let Hnext := fun p x => (deltaNext ^ 2)⁻¹ •
      (hstar p x - inducedMetric (I := 𝓘(ℝ, Esource)) (fun y => G (p, y) + U (p, y)) x)
    ∀ p x, deltaNext ^ 2 • (Hnext p x - h0 p x) =
      delta ^ 2 • (H p x - SH p x) - E p x -
        metricCrossTerm (I := 𝓘(ℝ, Esource))
          (fun y => G (p, y) - SG (p, y)) (fun y => U (p, y)) x := by
  dsimp only
  let mu := (volume : Measure (Eparameter × Esource))
  let K := fixedSmoothingKernel mu rho hrho r
  let chi := parameterLocalProductCutoff A B
    (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
  let H := fun p x => (delta ^ 2)⁻¹ •
    (hstar p x - inducedMetric (I := 𝓘(ℝ, Esource)) (fun y => G (p, y)) x)
  let SG := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi G
  let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
  let E := incrementsOriginalMetricError SG U
    (fun p x => SH p x - (deltaNext / delta) ^ 2 • h0 p x) delta
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  obtain ⟨Bc, hBc, hprep⟩ := exists_uniform_local_product_smoothing_providers
    (Es := Esource) (Ep := Eparameter) (M := M) (P := P)
    BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp
  obtain ⟨W, hW, hUW, hchi, hpart, hsupp, _hD, _hw, _ht⟩ :=
    hprep pcount A B hA hB univ RS RP
  have hGcoords := parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB G hG
  have hSG : ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ SG :=
    parameterLocalMapSmoothing_contMDiff (parameterLocalProductFamily A B)
      (parameterLocalProductFamily_chart_mem A B hA hB) mu hK.1 hK.2.1 hK.2.2.1
      hbuffer hell hell1 chi hchi hsupp G
      (parameterLocalMapInput_contDiffOn A B G hGcoords)
  intro p x
  have hinc : inducedMetric (I := 𝓘(ℝ, Esource))
      ((fun y => SG (p, y)) + (fun y => U (p, y))) x =
      inducedMetric (I := 𝓘(ℝ, Esource)) (fun y => SG (p, y)) x +
        delta ^ 2 • (SH p x - (deltaNext / delta) ^ 2 • h0 p x) + E p x := by
    dsimp only [E, incrementsOriginalMetricError]
    abel
  exact repair_normalized_defect_identity (fun y => G (p, y)) (fun y => SG (p, y))
    (fun y => U (p, y)) (parameterRound2_native_source_slice_contMDiff hG p)
    (parameterRound2_native_source_slice_contMDiff hSG p)
    (parameterRound2_native_source_slice_contMDiff hU p)
    x delta deltaNext hdelta hdeltaNext (hstar p x) (h0 p x) (SH p x) (E p x) hinc

#print axioms parameterRound2_actual_smoothing_defect_identity
end
end GlobalEmbedding.Continuation
