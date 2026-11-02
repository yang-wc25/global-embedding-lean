import GlobalEmbedding.Paper.PlanarPeriodOneCalculus
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Tactic.FinCases

/-!
# A genuine global unit binormal from actual independent Euclidean jets

Source: `main.tex`, `lem:planar`, line 265.
DAG: `planar-free-curve-unit-binormal`.
The cross product is Mathlib's actual algebraic cross product, transported to
the original Euclidean l² target. Its normalization is smooth because actual
linear independence makes this actual cross product nowhere zero.
-/

noncomputable section
open scoped Manifold ContDiff Matrix InnerProductSpace

namespace GlobalEmbedding.Paper

/-- Mathlib's true cross product, in the actual Euclidean target. -/
def spaceCurveCross (u v : SpaceCurve) : SpaceCurve :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

/-- Actual independent jets give a nonzero actual cross product. -/
theorem spaceCurveCross_ne_zero {u v : SpaceCurve}
    (h : LinearIndependent ℝ ![u, v]) : spaceCurveCross u v ≠ 0 := by
  have hpi : LinearIndependent ℝ ![WithLp.ofLp u, WithLp.ofLp v] := by
    rw [LinearIndependent.pair_iff] at h ⊢
    intro a b hab
    apply h a b
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    simpa only [map_add, map_smul, map_zero, PiLp.coe_continuousLinearEquiv] using hab
  have hn := crossProduct_ne_zero_iff_linearIndependent.mpr hpi
  intro he
  apply hn
  exact congrArg WithLp.ofLp he

/-- The genuine cross product is perpendicular to the first actual jet. -/
theorem spaceCurveCross_inner_left (u v : SpaceCurve) :
    ⟪spaceCurveCross u v, u⟫_ℝ = 0 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, spaceCurveCross,
    WithLp.ofLp_toLp, star_trivial] using
      (dot_self_cross (WithLp.ofLp u) (WithLp.ofLp v))

/-- The genuine cross product is perpendicular to the second actual jet. -/
theorem spaceCurveCross_inner_right (u v : SpaceCurve) :
    ⟪spaceCurveCross u v, v⟫_ℝ = 0 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, spaceCurveCross,
    WithLp.ofLp_toLp, star_trivial] using
      (dot_cross_self (WithLp.ofLp u) (WithLp.ofLp v))

/-- The actual normalized cross product, globally defined. -/
def spaceCurveUnitBinormal (u v : SpaceCurve) : SpaceCurve :=
  ‖spaceCurveCross u v‖⁻¹ • spaceCurveCross u v

/-- Actual independence proves all three unit-binormal identities. -/
theorem spaceCurveUnitBinormal_spec {u v : SpaceCurve}
    (h : LinearIndependent ℝ ![u, v]) :
    ‖spaceCurveUnitBinormal u v‖ = 1 ∧
      ⟪spaceCurveUnitBinormal u v, u⟫_ℝ = 0 ∧
      ⟪spaceCurveUnitBinormal u v, v⟫_ℝ = 0 := by
  refine ⟨NormedSpace.norm_normalize (spaceCurveCross_ne_zero h), ?_, ?_⟩
  · simp only [spaceCurveUnitBinormal, real_inner_smul_left,
      spaceCurveCross_inner_left, mul_zero]
  · simp only [spaceCurveUnitBinormal, real_inner_smul_left,
      spaceCurveCross_inner_right, mul_zero]

section Smooth

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]

/-- The actual cross product of two native smooth vector-valued maps is smooth. -/
theorem spaceCurveCross_contMDiff {u v : M → SpaceCurve}
    (hu : ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ u)
    (hv : ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ v) :
    ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ (fun x ↦ spaceCurveCross (u x) (v x)) := by
  have hu' (i : Fin 3) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ u x i) :=
    (EuclideanSpace.proj i).contMDiff.comp hu
  have hv' (i : Fin 3) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ v x i) :=
    (EuclideanSpace.proj i).contMDiff.comp hv
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff.comp
  apply contMDiff_pi_module_iff.mpr
  intro i
  fin_cases i
  · exact ((hu' 1).mul (hv' 2)).sub ((hu' 2).mul (hv' 1))
  · exact ((hu' 2).mul (hv' 0)).sub ((hu' 0).mul (hv' 2))
  · exact ((hu' 0).mul (hv' 1)).sub ((hu' 1).mul (hv' 0))

/-- The normalized genuine cross product supplies a global native smooth unit
binormal for any two actual smooth everywhere-independent derivative fields. -/
theorem spaceCurveUnitBinormal_contMDiff {u v : M → SpaceCurve}
    (hu : ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ u)
    (hv : ContMDiff I 𝓘(ℝ, SpaceCurve) ∞ v)
    (hfree : ∀ x, LinearIndependent ℝ ![u x, v x]) :
    ContMDiff I 𝓘(ℝ, SpaceCurve) ∞
      (fun x ↦ spaceCurveUnitBinormal (u x) (v x)) := by
  have hc := spaceCurveCross_contMDiff hu hv
  have hn : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x ↦ ‖spaceCurveCross (u x) (v x)‖) := by
    intro x
    exact (contDiffAt_norm ℝ (spaceCurveCross_ne_zero (hfree x))).comp_contMDiffAt
      (f := fun y : M ↦ spaceCurveCross (u y) (v y)) (hc x)
  exact (hn.inv₀ (fun x ↦ norm_ne_zero_iff.mpr
    (spaceCurveCross_ne_zero (hfree x)))).smul hc

end Smooth
end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.spaceCurveCross_ne_zero
#print axioms GlobalEmbedding.Paper.spaceCurveUnitBinormal_spec
#print axioms GlobalEmbedding.Paper.spaceCurveUnitBinormal_contMDiff
