import GlobalEmbedding.Paper.IncrementsModeFirstOrderCoefficients
import GlobalEmbedding.Paper.TrueSecondFormChart
import GlobalEmbedding.Paper.FixedChartDerivativeInjective
import GlobalEmbedding.Paper.FixedChartNormalRange
import GlobalEmbedding.Paper.SmoothFrameNormalProjection
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Original local coordinate geometry regularity for (6.2)

Source: `main.tex`, lem:increments, lines 617–643.
DAG: `increments-mode-coordinate-geometry-regularity`. Exclusive worker W2.
Only original local immersion is used; F stays on its original manifold.
Uniform weighted estimates and the remaining actual J/A/B regularity are separate.
-/

noncomputable section
open Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

/-- Actual inverse-chart coordinate directions give precisely the original projected
coordinate Hessian in the SAME true second form. Reuse the accepted true-form chart
formula and native inverse-chart differential cancellation. Source: B in (6.2). -/
theorem incrementsModeSecondForm_chart (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M) (x : D)
    (hx : x ∈ (extChartAt 𝓙 y).target) (i j : Fin (m + 1)) :
    (incrementsModeSecondForm F hF (extChartAt 𝓙 y).symm x i j : V) =
      (normalSpace (I := 𝓙) F ((extChartAt 𝓙 y).symm x)).starProjection
        (fderiv ℝ (fderiv ℝ (F ∘ (extChartAt 𝓙 y).symm)) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  let e := extChartAt 𝓙 y
  have hcoord (v : Fin (m + 1)) :
      mfderiv 𝓙 𝓙 e (e.symm x)
        (incrementsModeCoordinateDirections e.symm x v) = EuclideanSpace.single v 1 := by
    change mfderiv 𝓙 𝓙 e (e.symm x)
      (mfderiv 𝓙 𝓙 e.symm x (EuclideanSpace.single v 1)) = EuclideanSpace.single v 1
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓙) hx
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at h
    exact congrArg (fun L ↦ L (EuclideanSpace.single v 1)) h
  dsimp only [incrementsModeSecondForm]
  rw [← trueSecondForm_chart F hF (e.symm x) (chartAt D y)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓙) (n := 2) y)
    (by simpa only [e, extChartAt_source] using e.map_target hx)]
  change (normalSpace (I := 𝓙) F (e.symm x)).starProjection
    (fderiv ℝ (fderiv ℝ (F ∘ e.symm)) (e (e.symm x))
      (mfderiv 𝓙 𝓙 e (e.symm x) (incrementsModeCoordinateDirections e.symm x i))
      (mfderiv 𝓙 𝓙 e (e.symm x) (incrementsModeCoordinateDirections e.symm x j))) = _
  rw [hcoord i, hcoord j, e.right_inv hx]

/-- Actual original normal projection is smooth on any open subdomain of the actual
chart target where the ORIGINAL immersion differential is injective.
Source: the original local free geometry before (6.2). -/
theorem incrementsModeNormalProjection_contDiffOn (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M) (Ω : Set D) (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ x ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm x))) :
    ContDiffOn ℝ ∞
      (fun x ↦ (normalSpace (I := 𝓙) F ((extChartAt 𝓙 y).symm x)).starProjection) Ω := by
  have hFc : ContDiffOn ℝ ∞ (F ∘ (extChartAt 𝓙 y).symm) Ω :=
    ((hF.comp_contMDiffOn (contMDiffOn_extChartAt_symm y)).contDiffOn).mono hΩt
  have hD := hFc.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  have hi : ∀ x ∈ Ω, Function.Injective
      (fderiv ℝ (F ∘ (extChartAt 𝓙 y).symm) x) := by
    intro x hx
    exact fixed_chart_derivative_injective F y x (hΩt hx)
      (hF.mdifferentiable (by simp) _) (hinj x hx)
  apply (smooth_frame_normal_projection _ hD hi).congr
  intro x hx
  rw [normalSpace_eq_fixed_chart_range_orthogonal F y x (hΩt hx)
    (hF.mdifferentiable (by simp) _)]

/-- SAME induced Gamma is smooth from ORIGINAL smooth F and local immersion, not
from an assumed coefficient-regularity output. Reuse accepted Gram coefficient
smoothness and actual coordinate Hessian differentiation. Source: Gamma in (6.2). -/
theorem incrementsModeGamma_contDiffOn (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M) (Ω : Set D) (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ x ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm x))) (i j : Fin (m + 1)) :
    ContDiffOn ℝ ∞ (fun x ↦ incrementsModeGamma F (extChartAt 𝓙 y).symm x i j) Ω := by
  have hFc : ContDiffOn ℝ ∞ (F ∘ (extChartAt 𝓙 y).symm) Ω :=
    ((hF.comp_contMDiffOn (contMDiffOn_extChartAt_symm y)).contDiffOn).mono hΩt
  have hD := hFc.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  have hDD := hD.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  have hi : ∀ x ∈ Ω, Function.Injective
      (fderiv ℝ (F ∘ (extChartAt 𝓙 y).symm) x) := by
    intro x hx
    exact fixed_chart_derivative_injective F y x (hΩt hx)
      (hF.mdifferentiable (by simp) _) (hinj x hx)
  have hG := (smooth_frame_gram_coefficients _ hD.contMDiffOn hi).contDiffOn
  have hH := (hDD.clm_apply (contDiffOn_const (c := EuclideanSpace.single i 1))).clm_apply
    (contDiffOn_const (c := EuclideanSpace.single j 1))
  exact hG.clm_apply hH

/-- SAME ambient true-B coordinate row is smooth on the ORIGINAL local immersion
domain. Use the proved actual chart identity and the accepted normal-projection
regularity, with the actual smooth coordinate Hessian. Source: true B in (6.2). -/
theorem incrementsModeSecondForm_contDiffOn (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M) (Ω : Set D) (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ x ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm x))) (i j : Fin (m + 1)) :
    ContDiffOn ℝ ∞
      (fun x ↦ (incrementsModeSecondForm F hF (extChartAt 𝓙 y).symm x i j : V)) Ω := by
  have hFc : ContDiffOn ℝ ∞ (F ∘ (extChartAt 𝓙 y).symm) Ω :=
    ((hF.comp_contMDiffOn (contMDiffOn_extChartAt_symm y)).contDiffOn).mono hΩt
  have hD := hFc.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  have hDD := hD.fderiv_of_isOpen hΩ (m := ∞) (by simp)
  have hH := (hDD.clm_apply (contDiffOn_const (c := EuclideanSpace.single i 1))).clm_apply
    (contDiffOn_const (c := EuclideanSpace.single j 1))
  have hP := incrementsModeNormalProjection_contDiffOn F hF y Ω hΩ hΩt hinj
  apply (hP.clm_apply hH).congr
  intro x hx
  exact incrementsModeSecondForm_chart F hF y x (hΩt hx) i j

/-- Actual h=0 source is smooth from the ORIGINAL smooth normal amplitude and local
immersion geometry. Its J h_H term is genuinely zero; no coefficient/source output
smoothness is assumed. Source: k for the primary homogeneous mode in (6.2). -/
theorem incrementsModeSource_zero_contDiffOn (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M) (Ω : Set D) (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ x ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm x)))
    (vf : (x : D) → normalSpace (I := 𝓙) F ((extChartAt 𝓙 y).symm x))
    (hvf : ContDiffOn ℝ ∞ (fun x ↦ (vf x : V)) Ω) :
    ContDiffOn ℝ ∞
      (fun x ↦ incrementsModeSource F hF (extChartAt 𝓙 y).symm (fun _ _ _ ↦ 0) vf x) Ω := by
  let g : D → Fin (m + 1) → ℝ := fun x i ↦ incrementsModeRowWeight i *
    inner ℝ (incrementsModeSecondForm F hF (extChartAt 𝓙 y).symm x 0 i : V) (vf x : V)
  have hg : ContDiffOn ℝ ∞ g Ω := by
    apply contDiffOn_pi.mpr
    intro i
    exact contDiffOn_const.mul
      ((incrementsModeSecondForm_contDiffOn F hF y Ω hΩ hΩt hinj 0 i).inner ℝ hvf)
  have h := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.contDiff.comp_contDiffOn hg
  apply h.congr
  intro x hx
  have hz : incrementsModeTransverseSource (fun _ _ _ ↦ 0) x = 0 := rfl
  have hJzero : incrementsModeCoordinateJ F hF (extChartAt 𝓙 y).symm x 0 = 0 := map_zero _
  dsimp only [incrementsModeSource]
  rw [hz, hJzero]
  ext i
  change Fin.cases (0 / 2 : ℝ) (fun _ ↦ 0) i + incrementsModeRowWeight i *
      inner ℝ (incrementsModeSecondForm F hF (extChartAt 𝓙 y).symm x 0 i : V) (vf x : V) -
      (incrementsModeRowWeight i / 2) *
        inner ℝ (incrementsModeSecondForm F hF (extChartAt 𝓙 y).symm x 0 i : V) (0 : V) = _
  have h0 : Fin.cases (0 / 2 : ℝ) (fun _ : Fin m ↦ (0 : ℝ)) i = (0 : ℝ) := by
    refine Fin.cases ?_ (fun a ↦ ?_) i <;> norm_num
  rw [h0, zero_add, inner_zero_right, mul_zero, sub_zero]
  rfl

/-- The SAME two real normal-amplitude channels give a smooth original complex
h=0 source, on the already used native finite complex target. No complex normal
bundle or substitute source is constructed. Source: original complex (6.2). -/
theorem incrementsModeComplexSource_zero_contDiffOn (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (y : M) (Ω : Set D) (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt 𝓙 y).target)
    (hinj : ∀ x ∈ Ω, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) F ((extChartAt 𝓙 y).symm x)))
    (vfR vfI : (x : D) → normalSpace (I := 𝓙) F ((extChartAt 𝓙 y).symm x))
    (hvfR : ContDiffOn ℝ ∞ (fun x ↦ (vfR x : V)) Ω)
    (hvfI : ContDiffOn ℝ ∞ (fun x ↦ (vfI x : V)) Ω) :
    ContDiffOn ℝ ∞ (fun x ↦ incrementsModeComplexInclude
      (incrementsModeSource F hF (extChartAt 𝓙 y).symm (fun _ _ _ ↦ 0) vfR x) +
      Complex.I • incrementsModeComplexInclude
        (incrementsModeSource F hF (extChartAt 𝓙 y).symm (fun _ _ _ ↦ 0) vfI x)) Ω := by
  have hr := incrementsModeSource_zero_contDiffOn F hF y Ω hΩ hΩt hinj vfR hvfR
  have hi := incrementsModeSource_zero_contDiffOn F hF y Ω hΩ hΩt hinj vfI hvfI
  exact (incrementsModeComplexInclude.contDiff.comp_contDiffOn hr).add
    ((incrementsModeComplexInclude.contDiff.comp_contDiffOn hi).const_smul Complex.I)

end GlobalEmbedding.Paper
