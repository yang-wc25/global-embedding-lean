import Smoothing.ParameterRound2RepairNormAlgebra
import Smoothing.ParameterRound2RepairRegularity

/-!
# The actual nonlinear repair update in the original full-joint weighted norm

All maps, defects and the finite-increment metric error are literal native
objects. The actual induced-metric identity proves (6.6), and the original
weighted triangle inequality gives the displayed three-term recurrence.
Joint smoothness and true compact coordinate control prove every fixed-order
finiteness guard. No ErrorStep, metric-error estimate, or normalized defect
identity is a hypothesis. The concrete smoother is substituted by the next
consumer, so the map used by the increment and by the cross term is identical.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2RepairNormIdentityChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2RepairNormIdentityIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_actual_repair_weighted_norm_identity
    (A : BufferedAtlas M Es) (B : Fin pcount → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSK : ∀ i, S i ⊆ incrementsOriginalEvaluation A B Omega Q univ i)
    (G SG U F0 : P × M → Ey)
    (hG : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ G)
    (hSG : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ SG)
    (hU : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ U)
    (hF0 : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F0)
    (hstar SH : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hstarSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B hstar i)
      (incrementsOriginalDifferentiation A B i))
    (hSH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B SH i)
      (incrementsOriginalDifferentiation A B i))
    (delta deltaNext : ℝ) (hdelta : delta ≠ 0) (hdeltaNext : deltaNext ≠ 0)
    (m : ℕ) (tau : ℝ) (htau : 0 < tau) :
    let h0 := fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x
    let H := fun p x => (delta^2)⁻¹ •
      (hstar p x-inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G (p,y)) x)
    let E := incrementsOriginalMetricError SG U (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) delta
    let cross := fun p x => metricCrossTerm (I := 𝓘(ℝ, Es))
      (fun y => G (p,y)-SG (p,y)) (fun y => U (p,y)) x
    let Hnext := fun p x => (deltaNext^2)⁻¹ •
      (hstar p x-inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G (p,y)+U (p,y)) x)
    let W := fun T => paperAtlasWeighted 0 m tau (incrementsOriginalTensorCoordinates A B T)
      (incrementsOriginalDifferentiation A B) S
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ (fun z => G z+U z) ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B Hnext i)
      (incrementsOriginalDifferentiation A B i)) ∧
    W (fun p x => H p x-SH p x) ≠ ⊤ ∧ W E ≠ ⊤ ∧ W cross ≠ ⊤ ∧
    W (fun p x => Hnext p x-h0 p x) ≠ ⊤ ∧
    (W (fun p x => Hnext p x-h0 p x)).toReal ≤
      (deltaNext^2)⁻¹ * (delta^2 * (W (fun p x => H p x-SH p x)).toReal +
        (W E).toReal + (W cross).toReal) := by
  dsimp only
  let h0 := fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x
  let H := fun p x => (delta^2)⁻¹ •
    (hstar p x-inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G (p,y)) x)
  let E := incrementsOriginalMetricError SG U (fun p x => SH p x-(deltaNext/delta)^2 • h0 p x) delta
  let cross := fun p x => metricCrossTerm (I := 𝓘(ℝ, Es))
    (fun y => G (p,y)-SG (p,y)) (fun y => U (p,y)) x
  let Hnext := fun p x => (deltaNext^2)⁻¹ •
    (hstar p x-inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G (p,y)+U (p,y)) x)
  let O := incrementsOriginalDifferentiation A B
  let K := incrementsOriginalEvaluation A B Omega Q univ
  let f := incrementsOriginalTensorCoordinates A B (fun p x => H p x-SH p x)
  let g := incrementsOriginalTensorCoordinates A B E
  let h := incrementsOriginalTensorCoordinates A B cross
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B
  have hK : ∀ i, IsCompact (K i) := parameterRound2_originalEvaluation_univ_compact
    A B Omega Q hOmega hQ hOmegaTarget hQTarget
  have hKO : ∀ i, K i ⊆ O i := fun _ _ hy => hy.1
  have hSO : ∀ i, S i ⊆ O i := fun i => (hSK i).trans (hKO i)
  have hGnext := parameterRound2_native_add_contMDiff G U hG hU
  have hHnext := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn
    A B hA hB (fun z => G z+U z) hGnext hstar hstarSmooth deltaNext
  have hH := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn A B hA hB G hG hstar hstarSmooth delta
  have hh0 := parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B hA hB F0 hF0
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) := fun i => (hH i).sub (hSH i)
  have hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i) :=
    parameterRound2_actualMetricError_originalCoordinates_contDiffOn A B hA hB SG U hSG hU _
      (fun i => (hSH i).sub ((hh0 i).const_smul ((deltaNext/delta)^2))) delta
  have hh : ∀ i, ContDiffOn ℝ ∞ (h i) (O i) :=
    parameterRound2_cross_originalCoordinates_contDiffOn A B hA hB (fun z => G z-SG z) U
      (parameterRound2_native_sub_contMDiff G SG hG hSG) hU
  have hffinite := parameterRound2_paperAtlasWeighted_finite_of_compact f O S K hO hK hSK hKO hf 0 m tau
  have hgfinite := parameterRound2_paperAtlasWeighted_finite_of_compact g O S K hO hK hSK hKO hg 0 m tau
  have hhfinite := parameterRound2_paperAtlasWeighted_finite_of_compact h O S K hO hK hSK hKO hh 0 m tau
  have hid : ∀ p x, deltaNext^2 • (Hnext p x-h0 p x) =
      delta^2 • (H p x-SH p x)-E p x-cross p x := by
    intro p x
    have hinc : inducedMetric (I := 𝓘(ℝ, Es)) ((fun y => SG (p,y))+(fun y => U (p,y))) x =
        inducedMetric (I := 𝓘(ℝ, Es)) (fun y => SG (p,y)) x +
          delta^2 • (SH p x-(deltaNext/delta)^2 • h0 p x)+E p x := by
      dsimp only [E,incrementsOriginalMetricError]
      abel
    exact repair_normalized_defect_identity (fun y => G (p,y)) (fun y => SG (p,y)) (fun y => U (p,y))
      (parameterRound2_native_source_slice_contMDiff hG p)
      (parameterRound2_native_source_slice_contMDiff hSG p)
      (parameterRound2_native_source_slice_contMDiff hU p)
      x delta deltaNext hdelta hdeltaNext (hstar p x) (h0 p x) (SH p x) (E p x) hinc
  have hfield : (fun p x => Hnext p x-h0 p x) = fun p x =>
      (deltaNext^2)⁻¹ • (delta^2 • (H p x-SH p x)-E p x-cross p x) := by
    funext p x
    have hz := congrArg (fun T => (deltaNext^2)⁻¹ • T) (hid p x)
    simpa only [smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hdeltaNext),one_smul] using hz
  have hcoord : incrementsOriginalTensorCoordinates A B (fun p x => Hnext p x-h0 p x) =
      fun i x => (deltaNext^2)⁻¹ • (delta^2 • f i x-g i x-h i x) := by
    rw [hfield]
    rfl
  have hnorm := parameterRound2_paperAtlasWeighted_normalized_three_terms m htau f g h O S hO hSO
    hf hg hh hffinite hgfinite hhfinite (delta^2) ((deltaNext^2)⁻¹) (sq_nonneg _) (by positivity)
  refine ⟨hGnext,hHnext,hffinite,hgfinite,hhfinite,?_,?_⟩
  · change paperAtlasWeighted 0 m tau
      (incrementsOriginalTensorCoordinates A B (fun p x => Hnext p x-h0 p x)) O S ≠ ⊤
    rw [hcoord]
    exact hnorm.1
  · change (paperAtlasWeighted 0 m tau
      (incrementsOriginalTensorCoordinates A B (fun p x => Hnext p x-h0 p x)) O S).toReal ≤ _
    rw [hcoord]
    exact hnorm.2

#print axioms parameterRound2_actual_repair_weighted_norm_identity
end
end GlobalEmbedding.Continuation
