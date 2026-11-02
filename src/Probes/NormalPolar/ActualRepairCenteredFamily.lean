import NormalPolar.ActualRepairParameterBall
import NormalPolar.ActualRepairModelChart
import Smoothing.TensorLocalPrepared

/-!
# Centered original parameter balls for the actual repair map

The original preparation itself provides a chart containing the chosen
parameter.  Pulling back the actual family through that chart gives a
positive Pi-norm ball centred at zero.  The chart centre is retained; it is
not assumed to have zero coordinates.  Both joint smoothness and the actual
metric identity are proved for the very same pulled-back map.

This constructs a radius before choosing a scale or an iteration.  It does
not reduce the radius of any previously supplied probe family.
-/

noncomputable section
open Set Filter Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {n d N : ℕ} {ι M P : Type*} [Fintype ι]
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Fin d → ℝ
local notation "IM" => 𝓘(ℝ, Es)

local instance centeredRepairProductChart : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance centeredRepairProductManifold : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := IM) (n := ∞) P M

/-- A genuine plateau in the given preparation chooses the chart. -/
theorem actualRepairParameter_inner_of_preparation
    (B : TensorBufferedChartFamily ι P Ep) (K : Set P)
    (B₀ T : ℕ → ℝ) (D : ℕ) (prep : TensorLocalRawPreparation B K B₀ T D)
    (p₀ : P) (hp₀ : p₀ ∈ K) : ∃ b, p₀ ∈ B.inner b := by
  obtain ⟨b, hb⟩ := prep.plateau_on p₀ hp₀
  refine ⟨b, prep.inner_support b (subset_tsupport (prep.raw b) ?_)⟩
  change prep.raw b p₀ ≠ 0
  rw [hb]
  exact one_ne_zero

/-- The same actual map, on a centered parameter ball. -/
def actualRepairCenteredFamily (B : TensorBufferedChartFamily ι P Ep)
    (b : ι) (p₀ : P) (F : P × M → Ey) (u : X) (x : M) : Ey :=
  F (actualRepairParameterMap B b p₀ u, x)

theorem actualRepairCenteredFamily_zero
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (hp₀ : p₀ ∈ B.inner b) (F : P × M → Ey) :
    actualRepairCenteredFamily B b p₀ F 0 = fun x ↦ F (p₀, x) := by
  funext x
  simp only [actualRepairCenteredFamily, actualRepairParameterMap_zero B b p₀ hp₀]

/-- Translation in actual chart coordinates is an exact map identity. -/
theorem actualRepairCenteredFamily_eq_chartFamily
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (F : P × M → Ey) (u : X) :
    actualRepairCenteredFamily B b p₀ F u =
      actualRepairModelChartFamily (B.chart b) F
        ((EuclideanSpace.equiv (Fin d) ℝ) (B.chart b p₀) + u) := by
  funext x
  simp only [actualRepairCenteredFamily, actualRepairParameterMap,
    actualRepairModelChartFamily, map_add, ContinuousLinearEquiv.symm_apply_apply]

/-- Joint regularity is inherited from the actual repaired map and the
actual parameter chart, throughout the entire new original ball. -/
theorem actualRepairCenteredFamily_smooth
    (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ b, B.chart b ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F) :
    ContMDiffOn ((𝓘(ℝ, X)).prod IM) 𝓘(ℝ, Ey) ∞
      (Function.uncurry (actualRepairCenteredFamily B b p₀ F))
      (Metric.ball 0 (actualRepairParameterRadius B) ×ˢ univ) := by
  have hp : ContMDiffOn ((𝓘(ℝ, X)).prod IM) 𝓘(ℝ, Ep) ∞
      (fun z : X × M ↦ actualRepairParameterMap B b p₀ z.1)
      (Metric.ball 0 (actualRepairParameterRadius B) ×ˢ univ) :=
    (actualRepairParameterMap_smooth B hB b p₀ hp₀).comp contMDiffOn_fst
      (fun _ hz ↦ hz.1)
  have hj : ContMDiffOn ((𝓘(ℝ, X)).prod IM) 𝓘(ℝ, Ep × Es) ∞
      (fun z : X × M ↦ (actualRepairParameterMap B b p₀ z.1, z.2))
      (Metric.ball 0 (actualRepairParameterRadius B) ×ˢ univ) := by
    rw [modelWithCornersSelf_prod]
    exact hp.prodMk contMDiffOn_snd
  exact hF.comp_contMDiffOn hj

/-- No differentiation in the parameter chart changes a source metric:
this is the actual induced metric of the very same source slice. -/
theorem actualRepairCenteredFamily_metric
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (F : P × M → Ey)
    (g : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (hmetric : ∀ p, inducedMetric (I := IM) (fun x ↦ F (p, x)) = g p) (u : X) :
    inducedMetric (I := IM) (actualRepairCenteredFamily B b p₀ F u) =
      g (actualRepairParameterMap B b p₀ u) :=
  hmetric (actualRepairParameterMap B b p₀ u)

/-- The reference metric remains literally unchanged after parameter
pullback when the same repair trajectory has this constant metric. -/
theorem actualRepairCenteredFamily_reference_metric
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (F : P × M → Ey) (F₀ : M → Ey)
    (hmetric : ∀ p, inducedMetric (I := IM) (fun x ↦ F (p, x)) =
      inducedMetric (I := IM) F₀) (u : X) :
    inducedMetric (I := IM) (actualRepairCenteredFamily B b p₀ F u) =
      inducedMetric (I := IM) F₀ :=
  hmetric (actualRepairParameterMap B b p₀ u)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairParameter_inner_of_preparation
#print axioms GlobalEmbedding.NormalPolar.actualRepairCenteredFamily_smooth
#print axioms GlobalEmbedding.NormalPolar.actualRepairCenteredFamily_metric
