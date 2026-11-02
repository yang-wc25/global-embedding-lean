import Smoothing.ParameterRound2RepairScales

/-!
# Genuine joint regularity of the actual repair metric fields

All tensor fields here are defined from the actual native maps. Their
original full-joint coordinate smoothness is proved, so later finite-order
norms and the norm triangle inequality need no output-regularity hypotheses.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
noncomputable section

theorem parameterRound2_native_add_contMDiff
    {E H X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f g : X → Y) (hf : ContMDiff I 𝓘(ℝ,Y) ∞ f) (hg : ContMDiff I 𝓘(ℝ,Y) ∞ g) :
    ContMDiff I 𝓘(ℝ,Y) ∞ (fun x => f x+g x) :=
  (contDiff_fst.add contDiff_snd : ContDiff ℝ ∞ (fun z : Y×Y => z.1+z.2)).contMDiff.comp
    (hf.prodMk_space hg)

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2RepairRegularityChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2RepairRegularityIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_cross_originalCoordinates_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (F U : P × M → Ey)
    (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (hU : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ U) :
    ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B
      (fun p x => metricCrossTerm (I := 𝓘(ℝ, Es)) (fun z => F (p,z)) (fun z => U (p,z)) x) i)
      (incrementsOriginalDifferentiation A B i) := by
  have hfield : (fun p x => metricCrossTerm (I := 𝓘(ℝ, Es))
      (fun z => F (p,z)) (fun z => U (p,z)) x) =
      fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun z => F (p,z)+U (p,z)) x -
        inducedMetric (I := 𝓘(ℝ, Es)) (fun z => F (p,z)) x -
        inducedMetric (I := 𝓘(ℝ, Es)) (fun z => U (p,z)) x := by
    funext p x
    have h := inducedMetric_add (fun z => F (p,z)) (fun z => U (p,z))
      (parameterRound2_native_source_slice_contMDiff hF p)
      (parameterRound2_native_source_slice_contMDiff hU p) x
    change _ = inducedMetric (I := 𝓘(ℝ, Es)) ((fun z => F (p,z))+(fun z => U (p,z))) x-_-_
    rw [h]
    abel
  rw [hfield]
  have hf := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B hA hB F hF
  have hu := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B hA hB U hU
  have hsum := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B hA hB
    (fun z => F z+U z) (parameterRound2_native_add_contMDiff F U hF hU)
  exact fun i => ((hsum i).sub (hf i)).sub (hu i)

theorem parameterRound2_actualMetricError_originalCoordinates_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (F U : P × M → Ey)
    (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F)
    (hU : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ U)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B H i)
      (incrementsOriginalDifferentiation A B i)) (delta : ℝ) :
    ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B
      (incrementsOriginalMetricError F U H delta) i) (incrementsOriginalDifferentiation A B i) := by
  have hf := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B hA hB F hF
  have hsum := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B hA hB
    (fun z => F z+U z) (parameterRound2_native_add_contMDiff F U hF hU)
  exact fun i => ((hsum i).sub (hf i)).sub ((hH i).const_smul (delta^2))

theorem parameterRound2_normalizedDefect_originalCoordinates_contDiffOn
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (G : P × M → Ey) (hG : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ G)
    (hstar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hstarSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B hstar i)
      (incrementsOriginalDifferentiation A B i)) (delta : ℝ) :
    ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B
      (fun p x => (delta^2)⁻¹ •
        (hstar p x-inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G (p,y)) x)) i)
      (incrementsOriginalDifferentiation A B i) := by
  have hg := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B hA hB G hG
  exact fun i => ((hstarSmooth i).sub (hg i)).const_smul ((delta^2)⁻¹)

#print axioms parameterRound2_cross_originalCoordinates_contDiffOn
#print axioms parameterRound2_actualMetricError_originalCoordinates_contDiffOn
#print axioms parameterRound2_normalizedDefect_originalCoordinates_contDiffOn
end
end GlobalEmbedding.Continuation
