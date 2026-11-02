import GlobalEmbedding.Paper.TrueSecondFormChart
import GlobalEmbedding.Paper.SmoothImmersionNormalProjection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

open Bundle Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

set_option backward.isDefEq.respectTransparency false in
/-- In a fixed actual tangent frame, the true second form evaluated at two fixed
frame vectors is an actual normal-valued section whose ambient values are smooth
on that fixed chart source.

Proof: the fixed-coordinate first and second derivative fields are smooth on the
actual open chart target. Pull the second derivative back along the actual chart
and apply the proved actual smooth normal projection. The true-form chart theorem
identifies this projected Hessian with the actual trueSecondForm values, because
Mathlib's actual tangent trivialization is the actual chart differential and its
inverse frame cancels it. No claim is made about the frame's junk values off source.
Source: smooth true normal second form in `defn:phase`. -/
theorem true_second_form_fixed_frame_smooth
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x))
    (y : M) (u v : E) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun x ↦ (trueSecondForm f hf x
        (symmetricSquareProduct (TangentSpace I x)
          ((trivializationAt E (TangentSpace I) y).symmL ℝ x u)
          ((trivializationAt E (TangentSpace I) y).symmL ℝ x v)) :
            EuclideanSpace ℝ (Fin N))) (chartAt H y).source := by
  let F₀ := f ∘ (extChartAt I y).symm
  have hF : ContDiffOn ℝ ∞ F₀ (extChartAt I y).target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm y)).contDiffOn
  have hopen : IsOpen (extChartAt I y).target :=
    boundaryless_chart_target_open (I := I) (chartAt H y) (chart_mem_atlas H y)
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F₀) (extChartAt I y).target :=
    hF.fderiv_of_isOpen hopen (by simp)
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F₀)) (extChartAt I y).target :=
    hD.fderiv_of_isOpen hopen (by simp)
  have hmaps : MapsTo (extChartAt I y) (chartAt H y).source (extChartAt I y).target := by
    intro x hx
    exact (extChartAt I y).map_source (by simpa only [extChartAt_source] using hx)
  have hH := hDD.contMDiffOn.comp (contMDiffOn_extChartAt (I := I) (x := y)) hmaps
  have hHuv := (hH.clm_apply (contMDiffOn_const (c := u))).clm_apply
    (contMDiffOn_const (c := v))
  have hP := (smooth_immersion_normal_projection f hf hinj).contMDiffOn
    (s := (chartAt H y).source)
  have hproj := hP.clm_apply hHuv
  apply hproj.congr
  intro x hx
  let e := trivializationAt E (TangentSpace I) y
  have hcoord (a : E) :
      tangentSpaceCastModel 𝓘(ℝ, E) (extChartAt I y x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I y) x (e.symmL ℝ x a)) = a := by
    change mfderiv I 𝓘(ℝ, E) (extChartAt I y) x (e.symmL ℝ x a) = a
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hx]
    exact e.continuousLinearMapAt_symmL hx a
  have he := trueSecondForm_chart f hf x (chartAt H y)
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := 2) y) hx
    (e.symmL ℝ x u) (e.symmL ℝ x v)
  simp only [extChartAt] at hcoord
  rw [hcoord u, hcoord v] at he
  exact (congrArg (fun z : normalSpace (I := I) f x ↦
    (z : EuclideanSpace ℝ (Fin N))) he).symm

end GlobalEmbedding.Paper
