import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-!
# Joint real analyticity from translation parameters and bounded evaluation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. In the source, the analytic Banach-valued fixed point depends on a base
parameter and a translation parameter; evaluation at a fixed orbit point recovers the desired
jointly analytic function. Boundedness of the evaluation map is an explicit input here.
-/

open scoped Topology

namespace GlobalEmbedding.Paper

/-- A complex analytic parameter family with the translation-evaluation identity recovers a
jointly real analytic map in the original base and orbit coordinates.

Source: Proposition `prop:collar`, proof lines 530–534.
Restrict the complex power series to real scalars, compose with the real parameter inclusion
and the bounded real evaluation map, and obtain an analytic function of `(p,α)` at `(p₀,0)`.
Precompose with the analytic affine change `(p,y)↦(p,y-y₀)`. Its value at `(p₀,y₀)` is `(p₀,0)`.
Pulling back the eventual translation identity along that change identifies the resulting
analytic map with `u(p,y)`, since `y₀+(y-y₀)=y`. Analyticity is invariant under this local equality.
The real evaluation may include the real projection from a complexified target; no normed
function-space evaluation is implicitly assumed continuous.
-/
theorem collar_translation_joint_analytic
    {P Y Z E V : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℂ Z]
    [IsScalarTower ℝ ℂ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ψ : Z → E) (J : P × Y →L[ℝ] Z) (ev : E →L[ℝ] V)
    (u : P × Y → V) (p₀ : P) (y₀ : Y)
    (hψ : AnalyticAt ℂ ψ (J (p₀, 0)))
    (htranslation : ∀ᶠ z : P × Y in 𝓝 (p₀, 0),
      ev (ψ (J z)) = u (z.1, y₀ + z.2)) :
    AnalyticAt ℝ u (p₀, y₀) := by
  let shift : P × Y → P × Y := fun z ↦ (z.1, z.2 - y₀)
  have hshift : AnalyticAt ℝ shift (p₀, y₀) :=
    analyticAt_fst.prod (analyticAt_snd.sub analyticAt_const)
  have hshiftval : shift (p₀, y₀) = (p₀, 0) := by simp [shift]
  have hreal : AnalyticAt ℝ (fun z : P × Y ↦ ev (ψ (J z))) (p₀, 0) :=
    (ev.analyticAt _).comp
      ((hψ.restrictScalars (𝕜 := ℝ)).comp (J.analyticAt _))
  have hcomp : AnalyticAt ℝ (fun z : P × Y ↦ ev (ψ (J (shift z)))) (p₀, y₀) :=
    hreal.comp_of_eq hshift hshiftval
  apply hcomp.congr
  have ht : ∀ᶠ z : P × Y in 𝓝 (p₀, y₀),
      ev (ψ (J (shift z))) = u ((shift z).1, y₀ + (shift z).2) :=
    (hshift.continuousAt.tendsto.mono_right (by rw [hshiftval])).eventually htranslation
  filter_upwards [ht] with z hz
  simpa only [shift, add_sub_cancel] using hz

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_translation_joint_analytic
