import GlobalEmbedding.Paper.SmoothImmersionNormalProjection
import Upgrade.SupportedPartialHessianSmooth
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Joint smoothness of the true normal projection of an actual map family

Only joint smoothness of the map and injectivity of its actual source
differential are hypotheses. A fixed source chart identifies the true normal
space with the orthogonal complement of the actual spatial first jet. The
existing smooth-frame projection theorem then gives the joint projection.
The local expressions are identified with the same native normalSpace field.
-/

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {n N : ℕ} {M P : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- In a fixed actual source chart the normal projection is jointly smooth
in the original parameter and source variables. -/
theorem contDiffOn_joint_normalProjection_extChart
    (F : P → M → V) (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    {U : Set P} (hU : IsOpen U)
    (hjoint : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hinj : ∀ u ∈ U, ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F u) x))
    (y : M) :
    ContDiffOn ℝ ∞
      (fun z : P × E ↦ (normalSpace (I := IM) (F z.1)
        ((extChartAt IM y).symm z.2)).starProjection)
      (U ×ˢ (extChartAt IM y).target) := by
  have hopen : IsOpen (extChartAt IM y).target :=
    boundaryless_chart_target_open (I := IM) (chartAt E y) (chart_mem_atlas E y)
  have hfst : ContMDiffOn 𝓘(ℝ, P × E) 𝓘(ℝ, P) ∞
      (Prod.fst : P × E → P) (U ×ˢ (extChartAt IM y).target) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, P × E) 𝓘(ℝ, E) ∞
      (Prod.snd : P × E → E) (U ×ˢ (extChartAt IM y).target) :=
    contDiff_snd.contMDiff.contMDiffOn
  have hinv : ContMDiffOn 𝓘(ℝ, P × E) IM ∞
      (fun z : P × E ↦ (extChartAt IM y).symm z.2)
      (U ×ˢ (extChartAt IM y).target) :=
    (contMDiffOn_extChartAt_symm y).comp hsnd (fun _ hz ↦ hz.2)
  have hc : ContDiffOn ℝ ∞
      (fun z : P × E ↦ F z.1 ((extChartAt IM y).symm z.2))
      (U ×ˢ (extChartAt IM y).target) :=
    (hjoint.comp (hfst.prodMk hinv) (fun z hz ↦ ⟨hz.1, mem_univ _⟩)).contDiffOn
  have hD := contDiffOn_actual_spatial_fderiv (hU.prod hopen) hc
  have hi : ∀ z ∈ U ×ˢ (extChartAt IM y).target,
      Function.Injective (fderiv ℝ (F z.1 ∘ (extChartAt IM y).symm) z.2) := by
    intro z hz
    exact fixed_chart_derivative_injective (F z.1) y z.2 hz.2
      ((hF z.1).mdifferentiable (by simp) _) (hinj z.1 hz.1 _)
  have hp := smooth_normed_frame_normal_projection
    (fun z : P × E ↦ fderiv ℝ (F z.1 ∘ (extChartAt IM y).symm) z.2) hD hi
  apply hp.congr
  intro z hz
  rw [normalSpace_eq_fixed_chart_range_orthogonal (F z.1) y z.2 hz.2
    ((hF z.1).mdifferentiable (by simp) _)]

/-- The native true-normal projection of an actual jointly smooth family is
jointly smooth on its same open parameter domain and every source point. -/
theorem contMDiffOn_joint_normalProjection
    (F : P → M → V) (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    {U : Set P} (hU : IsOpen U)
    (hjoint : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hinj : ∀ u ∈ U, ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ, V) (F u) x)) :
    ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : P × M ↦ (normalSpace (I := IM) (F z.1) z.2).starProjection)
      (U ×ˢ univ) := by
  intro z hz
  have hopen : IsOpen (extChartAt IM z.2).target :=
    boundaryless_chart_target_open (I := IM) (chartAt E z.2) (chart_mem_atlas E z.2)
  have hpoint : (z.1, extChartAt IM z.2 z.2) ∈ U ×ˢ (extChartAt IM z.2).target :=
    ⟨hz.1, mem_extChartAt_target (I := IM) z.2⟩
  have hc := (contDiffOn_joint_normalProjection_extChart F hF hU hjoint hinj z.2).contDiffAt
    ((hU.prod hopen).mem_nhds hpoint)
  have hfst : ContMDiffAt ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, P) ∞
      (Prod.fst : P × M → P) z := contMDiffAt_fst
  have hsnd : ContMDiffAt ((𝓘(ℝ, P)).prod IM) IM ∞
      (Prod.snd : P × M → M) z := contMDiffAt_snd
  have hchart := (contMDiffAt_extChartAt (I := IM) (x := z.2)).comp z hsnd
  have hcomp := ContDiffAt.comp_contMDiffAt
    (f := fun w : P × M ↦ (w.1, extChartAt IM z.2 w.2)) (x := z)
    hc (hfst.prodMk_space hchart)
  have hp : ContMDiffAt ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun w : P × M ↦ (normalSpace (I := IM) (F w.1) w.2).starProjection) z := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := IM) z.2).mem_nhds (mem_extChartAt_source z.2))]
      with w hw
    simp only [Function.comp_apply, (extChartAt IM z.2).left_inv hw]
  exact hp.contMDiffWithinAt

end GlobalEmbedding.NormalPolar
