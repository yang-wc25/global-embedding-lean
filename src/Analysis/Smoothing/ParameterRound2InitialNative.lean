import Smoothing.ParameterRound2InitialAlgebra
import Smoothing.ParameterRound2MetricRegularity
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Actual native initialization in the original full-joint pair norm

G0 is the literal square-root contraction of F0. H0 is defined from the
actual induced metric of G0 and the target hstar, and its decomposition
is proved using the native metric scaling theorem. All norms use the true
original coordinate views, including the parameter derivatives.
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

local instance parameterRound2InitialNativeChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2InitialNativeIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- The actual original (6.9) map and normalized metric defect satisfy the
native smoothness, exact normalization and the original weighted entrance
budget. The only target-error norm is order m, not m+2. -/
theorem parameterRound2_initial_native_pair
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (S : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (F0 : P × M → Ey) (hF0 : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F0)
    (hstar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hstarSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart hstar i)
      (incrementsOriginalDifferentiation A B.chart i))
    (m : ℕ) (t delta : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdelta : delta ≠ 0) (hsmall : delta ^ 2 ≤ 1)
    (hfFinite : paperAtlasCj (m+2) (incrementsOriginalMapCoordinates A B.chart F0)
      (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤)
    (hgFinite : paperAtlasCj m (incrementsOriginalTensorCoordinates A B.chart
      (fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x))
      (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤)
    (heFinite : paperAtlasCj m (incrementsOriginalTensorCoordinates A B.chart
      (fun p x => hstar p x - inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x))
      (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤) :
    let h0 := fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x
    let G0 := fun z => Real.sqrt (1-delta^2) • F0 z
    let H0 := fun p x => (delta^2)⁻¹ •
      (hstar p x - inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G0 (p,y)) x)
    (∀ p x, H0 p x = h0 p x + (delta^2)⁻¹ • (hstar p x - h0 p x)) ∧
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ G0 ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H0 i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    parameterLocalOriginalTotalPairWeighted A B G0 H0 m t S ≠ ⊤ ∧
    (parameterLocalOriginalTotalPairWeighted A B G0 H0 m t S).toReal ≤
      (parameterLocalOriginalTotalPairWeighted A B F0 h0 m t S).toReal +
        (delta^2)⁻¹ * (m+1) *
          (paperAtlasCj m (incrementsOriginalTensorCoordinates A B.chart
            (fun p x => hstar p x - h0 p x))
            (incrementsOriginalDifferentiation A B.chart) S).toReal := by
  dsimp only
  let h0 := fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x
  let G0 := fun z => Real.sqrt (1-delta^2) • F0 z
  let H0 := fun p x => (delta^2)⁻¹ •
    (hstar p x - inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G0 (p,y)) x)
  let f := incrementsOriginalMapCoordinates A B.chart F0
  let g := incrementsOriginalTensorCoordinates A B.chart h0
  let e := incrementsOriginalTensorCoordinates A B.chart (fun p x => hstar p x - h0 p x)
  let O := incrementsOriginalDifferentiation A B.chart
  have hnormalize : ∀ p x, H0 p x = h0 p x + (delta^2)⁻¹ • (hstar p x - h0 p x) := by
    intro p x
    exact repair_initial_normalized_defect (fun y => F0 (p,y))
      (parameterRound2_native_source_slice_contMDiff hF0 p) delta hdelta hsmall x (hstar p x)
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i) :=
    parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i) := fun i => (hstarSmooth i).sub (hg i)
  have hGeq : incrementsOriginalMapCoordinates A B.chart G0 =
      fun i y => Real.sqrt (1-delta^2) • f i y := by
    funext i y
    exact (EuclideanSpace.equiv (Fin N) ℝ).map_smul _ _
  have hHeq : incrementsOriginalTensorCoordinates A B.chart H0 =
      fun i y => g i y + (delta^2)⁻¹ • e i y := by
    funext i y k
    dsimp only [incrementsOriginalTensorCoordinates]
    rw [hnormalize]
    rfl
  have hHsmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H0 i) (O i) := by
    rw [hHeq]
    exact fun i => (hg i).add ((he i).const_smul _)
  have hc : |Real.sqrt (1-delta^2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg delta])
  have hbudget := parameterRound2_initial_coordinate_pair_budget m ht ht1 f g e O S
    (parameterRound2_originalDifferentiation_open A B.chart) hSO hf hg he hfFinite hgFinite heFinite
    (Real.sqrt (1-delta^2)) ((delta^2)⁻¹) hc (inv_nonneg.mpr (sq_nonneg _))
  change _ ≠ ⊤ ∧ _ ≤ _ at hbudget
  have hWf := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 m t f O S hfFinite
  have hWg := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 m t g O S (by simpa using hgFinite)
  have hG0 : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ G0 :=
    ((contDiff_id : ContDiff ℝ ∞ (fun y : Ey => y)).const_smul
      (Real.sqrt (1-delta^2))).contMDiff.comp hF0
  refine ⟨hnormalize, hG0, hHsmooth, ?_, ?_⟩
  · change (paperAtlasWeighted 2 m t (incrementsOriginalMapCoordinates A B.chart G0) O S +
      paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H0) O S) ≠ ⊤
    rw [hGeq,hHeq]
    exact hbudget.1
  · change (paperAtlasWeighted 2 m t (incrementsOriginalMapCoordinates A B.chart G0) O S +
      paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H0) O S).toReal ≤
        (paperAtlasWeighted 2 m t f O S + paperAtlasWeighted 0 m t g O S).toReal + _
    rw [hGeq,hHeq,ENNReal.toReal_add hWf hWg]
    exact hbudget.2

#print axioms parameterRound2_initial_native_pair
end
end GlobalEmbedding.Continuation
